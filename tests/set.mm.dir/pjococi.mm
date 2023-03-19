include "ococi.mm"

theorem pjococi
  let cH: class H
  assume pjococ.1: |- H e. CH


  assert |- ( _|_ ` ( _|_ ` H ) ) = H

  proof
    cH
    pjococ.1
    ococi
end
