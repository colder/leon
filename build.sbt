name := "Leon"

version := "2.0"

organization := "ch.epfl.lara"

scalaVersion := "2.10.2"

scalacOptions += "-deprecation"

scalacOptions += "-unchecked"

scalacOptions += "-feature"

javacOptions += "-Xlint:unchecked"

if(System.getProperty("sun.arch.data.model") == "64") {
  unmanagedBase <<= baseDirectory { base => base / "unmanaged" / "64" }
} else {
  unmanagedBase <<= baseDirectory { base => base / "unmanaged" / "32" }
}

libraryDependencies += "junit" % "junit" % "4.8" % "test"

libraryDependencies += "com.novocode" % "junit-interface" % "0.10-M3" % "test"

resolvers += "Typesafe Repository" at "http://repo.typesafe.com/typesafe/releases/"

libraryDependencies ++= Seq(
    "org.scala-lang" % "scala-compiler" % "2.10.2",
    "org.scalatest" %% "scalatest" % "1.9.1" excludeAll(ExclusionRule(organization="org.scala-lang")),
    "com.typesafe.akka" %% "akka-actor" % "2.1.4"
)

fork in run := true

fork in test := true

EclipseKeys.skipParents in ThisBuild := false

libraryDependencies += "com.dongxiguo" %% "zero-log" % "0.1.2"

sound.play(compile in Compile, Sounds.Basso) // play the 'Basso' sound whenever compile completes (successful or not)
