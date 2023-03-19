include "c4.mm"
include "cdvds.mm"
include "wbr.mm"
include "c2.mm"
include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "2z.mm"
include "a1i.mm"
include "4z.mm"
include "dvdszrcl.mm"
include "simprd.mm"
include "3jca.mm"
include "z4even.mm"
include "jctl.mm"
include "dvdstr.mm"
include "sylc.mm"

theorem 4dvdseven
  let cN: class N


  assert |- ( 4 || N -> 2 || N )

  proof
    c4
    cN
    cdvds
    wbr
    #
    c2
    cz
    wcel
    #
    c4
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    c2
    c4
    cdvds
    wbr
    #
    @0
    wa
    c2
    cN
    cdvds
    wbr
    @0
    @1
    @2
    @3
    @1
    @0
    2z
    a1i
    @2
    @0
    4z
    a1i
    @0
    @2
    @3
    c4
    cN
    dvdszrcl
    simprd
    3jca
    @0
    @4
    z4even
    jctl
    c2
    c4
    cN
    dvdstr
    sylc
end
