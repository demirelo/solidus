object "Object" {
  code {
    function id(x) -> r {
      r := x
    }

    let x := id(1)
    switch x
    case 1 {
      datacopy(0, dataoffset("blob"), datasize("blob"))
    }
    default {
      stop()
    }
  }

  data "blob" hex"010203"

  object "Object_deployed" {
    code {
      return(0, 0)
    }
  }
}
