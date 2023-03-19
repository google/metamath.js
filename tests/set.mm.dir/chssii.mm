include "chshii.mm"
include "shssii.mm"

theorem chssii
  let cH: class H
  assume chssi.1: |- H e. CH


  assert |- H C_ ~H

  proof
    cH
    cH
    chssi.1
    chshii
    shssii
end
