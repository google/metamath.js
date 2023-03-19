include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "cc.mm"
include "zcn.mm"
include "mulcom.mm"
include "syl2anr.mm"
include "wi.mm"
include "zmulcl.mm"
include "w3a.mm"
include "dvds0lem.mm"
include "ex.mm"
include "3com12.mm"
include "mpd3an3.mm"
include "mpd.mm"

theorem dvdsmul1
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> M || ( M x. N ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    cN
    cM
    cmul
    co
    cM
    cN
    cmul
    co
    #
    wceq
    #
    cM
    @2
    cdvds
    wbr
    #
    @1
    cN
    cc
    wcel
    cM
    cc
    wcel
    @3
    @0
    cN
    zcn
    cM
    zcn
    cN
    cM
    mulcom
    syl2anr
    @0
    @1
    @2
    cz
    wcel
    #
    @3
    @4
    wi
    #
    cM
    cN
    zmulcl
    @1
    @0
    @5
    @6
    @1
    @0
    @5
    w3a
    @3
    @4
    cN
    cM
    @2
    dvds0lem
    ex
    3com12
    mpd3an3
    mpd
end
