import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

/**
* Small program used to generate routes for MoonRoute (lua files) and the verified and unverified router
*/
public class RoutesGenerator {

  public static int IPV4_ADDR_LENGTH = 4;

  public static int   MAX_OCTET_SIZE = 256;

  //proportion of routes with a prefix length bigger than 23
  public static double LONG_PREFIX_PROPORTION = 0.01;

  public static String PORT_NUMBER = "0";


  /**
  * Take number of routes to generate as command line parameters
  * @param args
  */
  public static void main(String[] args) {


    for (int i = 0; i < args.length; i++) {

	  int nbrRoutes = 0;

	  try {
        nbrRoutes = Integer.parseInt(args[i]);
	  } catch (NumberFormatException n) {
		System.out.println("PLease enter a number\n");
	  }


      try {
        createFile("Routes" + nbrRoutes, nbrRoutes);
      } catch (IOException e) {
        e.printStackTrace();
      }

    }


  }


  /**
  * Create config files for MoonRoute and the unverified-router
  * @param name name of the file to create
  * @param nbrRoutes the number of routes to generate
  * @throws IOException
  */
  public static void createFile(String name, long nbrRoutes) throws IOException {


    FileWriter fw = new FileWriter(new File(name));
    FileWriter fwLua = new FileWriter(new File(name+".lua"));


    //file up cfg.lua with defautl configurations

    fwLua.write("config = {ports = {}, routes = {}}\n" +
            "\n" +
            "\n" +
            "\t\t\t-- GENERAL CONFIGURATION\n" +
            "\t\t\tconfig[\"txQueueSize\"] = 128\n" +
            "\t\t\tconfig[\"txQueueTimeout\"] = 0.001\n" +
            "\t\t\tconfig[\"rxBurstSize\"] = 128\n" +
            "\t\t\tconfig[\"addRoutesToLocalNetworks\"] = false\n" +
            "\t\t\tconfig[\"telnetEnable\"] = false\n" +
            "\t\t\tconfig[\"telnetPort\"] = 23\n" +
            "\t\t\tconfig[\"telnetBindIP\"] = \"0.0.0.0\"\n" +
            "\t\t\tconfig[\"enableVirtualInterfaces\"] = false\n" +
            "\t\t\tconfig[\"virtualInterfacePrefix\"] = \"vEth-\"\n" +
            "\t\t\tconfig[\"useLinuxRoutingTable\"] = false\n" +
            "\t\t\tconfig[\"slowPathQueueSize\"] = 64\n" +
            "\t\t\tconfig[\"distributorQueuesSize\"] = 128 -- FIXME:is this option used at all?\n" +
            "\n" +
            "\n" +
            "\t\t\t-- PORT CONFIGURATION\n" +
            "\t\t\t-- configuration, which applies to all ports\n" +
            "\t\t\tconfig[\"fastPathCores\"] = {8}\n" +
            "\n" +
            "\t\t\t-- port wise configuration\n" +
            "\t\t\tports = {}\n" +
            "\n" +
            "\t\t\tports[\"Port1\"] = {\n" +
            "\t\t\t  mac = \"90:E2:BA:55:12:24\",\n" +
            "\t\t\t  ipv4 = \"10.0.2.1\",\n" +
            "\t\t\t  ipv4Prefix = 24,\n" +
            "\t\t\t  direction = \"inout\",\n" +
            "\t\t\t}\n" +
            "\n" +
            "\n" +
            "\t\t\t-- STATIC ROUTES CONFIGURATION\n" +
            "\t\t\troutes = {}\n");



    //add default routes

    fw.write("0.0.0.0,1,0\n");
    fw.write("1.0.0.0,1,0\n");


    fwLua.write("routes[\"Route1\"] = {\n" +
            "  \t\t\t\t   nhPort = \"Port1\",\n" +
            "  \t\t\t\t   --nhMAC = A0:36:9f:3b:6d:44,\n" +
            "\t\t\t\t   nhMAC = \"a0:36:9f:3b:5b:6c\",\n" +
            "\t\t\t\t   --nhIPv4 = 10.0.1.5,\n" +
            "\t\t\t\t   networkIP = \"0.0.0.0\",\n" +
            "\t\t\t\t   networkPrefix = 1\n" +
            "\t\t\t\t }\n" +
            "routes[\"Route2\"] = {\n" +
            "  \t\t\t\t   nhPort = \"Port1\",\n" +
            "  \t\t\t\t   --nhMAC = A0:36:9f:3b:6d:44,\n" +
            "\t\t\t\t   nhMAC = \"a0:36:9f:3b:5b:6c\",\n" +
            "\t\t\t\t   --nhIPv4 = 10.0.1.5,\n" +
            "\t\t\t\t   networkIP = \"1.0.0.0\",\n" +
            "\t\t\t\t   networkPrefix = 1\n" +
            "\t\t\t\t }");


	//add random routes
    double nbrShortPrefix = Math.floor( (1- LONG_PREFIX_PROPORTION) * nbrRoutes);


    for (int i = 0; i < nbrRoutes; i++) {
     
      String ip = getRandomIp();

      if (i < nbrShortPrefix) {
		
	    long prefixLength = Math.round((Math.random() * 22) + 1);

        fw.write(ip+","+prefixLength+","+PORT_NUMBER+"\n");


        fwLua.write("routes[\"Route"+(i+2)+"\"] = {\n" +
                "  \t\t\t\t   nhPort = \"Port1\",\n" +
                "  \t\t\t\t   --nhMAC = A0:36:9f:3b:6d:44,\n" +
                "\t\t\t\t   nhMAC = \"a0:36:9f:3b:5b:6c\",\n" +
                "\t\t\t\t   --nhIPv4 = 10.0.1.5,\n" +
                "\t\t\t\t   networkIP = \""+ip+"\",\n" +
                "\t\t\t\t   networkPrefix = "+prefixLength+"\n" +
                "\t\t\t\t }\n");

      } else {
		long prefixLength = Math.round((Math.random() * 8) + 24);


        fw.write(ip+","+prefixLength+","+PORT_NUMBER+"\n");

        fwLua.write("routes[\"Route"+(i+2)+"\"] = {\n" +
                "  \t\t\t\t   nhPort = \"Port1\",\n" +
                "  \t\t\t\t   --nhMAC = A0:36:9f:3b:6d:44,\n" +
                "\t\t\t\t   nhMAC = \"a0:36:9f:3b:5b:6c\",\n" +
                "\t\t\t\t   --nhIPv4 = \"10.0.1.5\",\n" +
                "\t\t\t\t   networkIP = \""+ip+"\",\n" +
                "\t\t\t\t   networkPrefix = "+prefixLength+"\n" +
                "\t\t\t\t }\n");

      }

    }



    //write final lines of cfg.lua

    fwLua.write("config.ports = ports\n" +
            "\t\t\tconfig.routes = routes\n" +
            "\n" +
            "\t\t\treturn config");



    fw.close();
    fwLua.close();

  }


  /**
  * @return a random ipv4 address
  */
  public static String getRandomIp() {


    StringBuilder sb = new StringBuilder();

    for (int i = 0; i < IPV4_ADDR_LENGTH; i++) {

      long octet = Math.round(Math.random() * (MAX_OCTET_SIZE - 1));

      if (i < IPV4_ADDR_LENGTH -1) {
        sb.append(octet + ".");
      } else {
        sb.append(octet);
      }

    }

    return sb.toString();
  }


}

