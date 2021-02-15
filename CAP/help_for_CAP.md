## CAP info functions

* CanCompute( category, string )
  Returns true if the the function with name <string> is computable in <category>.

* CheckConstructivenessOfCategory( category, string )
  Returns a list of names of basic operations which are not computable in <category> but
  needed to have the categorical property <string> completely constructive.

* InfoOfInstalledOperationsOfCategory( category )
  Returns the number of primitive and derived operations and lists all known categorical properties of <category>
  
* ListKnownCategoricalProperties( category )
  Lists all known categorical properties of <category>.

* InstalledMethodsOfCategory( category )
  Lists all installed methods of category.

* DerivationsOfMethodByCategory( category, method )
  Shows how <method> can be derived in <category>.

* ListInstalledOperationsOfCategory( category )
  Returns a list of strings of all installed operations of <category>.

* ListPrimitivelyInstalledOperationsOfCategory( category )
  Returns a list of strings of all primitively installed operations of <category>.

* ListCAPPrepareFunctions( )
  Lists all prepare functions currently available.

* PrintAutomaticallyGeneratedInstallationsForLimits( string )
  Prints all installations of the method with name <string> which are automatically generated
  by the (co)limit mechanism. If no method name is given, all such installations are printed.
