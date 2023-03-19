include "col.mm"
include "wcel.mm"
include "clat.mm"
include "cops.mm"
include "isolat.mm"
include "mpbir2an.mm"

theorem isolatiN
  let cK: class K
  assume isolati.1: |- K e. Lat
  assume isolati.2: |- K e. OP


  assert |- K e. OL

  proof
    cK
    col
    wcel
    cK
    clat
    wcel
    cK
    cops
    wcel
    isolati.1
    isolati.2
    cK
    isolat
    mpbir2an
end
