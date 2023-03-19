include "cv.mm"
include "wcel.mm"
include "cdm.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "wex.mm"
include "c0.mm"
include "wfn.mm"
include "w3a.mm"
include "wrex.mm"
include "bnj1436.mm"
include "simp1.mm"
include "reximi.mm"
include "fndm.mm"
include "3syl.mm"
include "bnj1196.mm"
include "cab.mm"
include "nfre1.mm"
include "nfab.mm"
include "nfcxfr.mm"
include "nfcri.mm"
include "19.37.mm"
include "mpbir.mm"
include "nfv.mm"
include "nfim.mm"
include "bnj529.mm"
include "eleq2.mm"
include "biimparc.mm"
include "sylan.mm"
include "imim2i.mm"
include "exlimi.mm"
include "ax-mp.mm"

theorem bnj900
  let wph: wff ph
  let wps: wff ps
  let cB: class B
  let cD: class D
  let vf: setvar f
  let vn: setvar n
  assume bnj900.3: |- D = ( _om \ { (/) } )
  assume bnj900.4: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }

  disjoint f n
  assert |- ( f e. B -> (/) e. dom f )

  proof
    vf
    cv
    #
    cB
    wcel
    #
    vn
    cv
    #
    cD
    wcel
    #
    @0
    cdm
    #
    @2
    wceq
    #
    wa
    #
    wi
    #
    vn
    wex
    #
    @1
    c0
    @4
    wcel
    #
    wi
    #
    @8
    @1
    @6
    vn
    wex
    wi
    @1
    @5
    vn
    cD
    @1
    @0
    @2
    wfn
    #
    wph
    wps
    w3a
    #
    vn
    cD
    wrex
    #
    @11
    vn
    cD
    wrex
    @5
    vn
    cD
    wrex
    @13
    vf
    cB
    bnj900.4
    bnj1436
    @12
    @11
    vn
    cD
    @11
    wph
    wps
    simp1
    reximi
    @11
    @5
    vn
    cD
    @2
    @0
    fndm
    reximi
    3syl
    bnj1196
    @1
    @6
    vn
    vn
    vf
    cB
    vn
    cB
    @13
    vf
    cab
    bnj900.4
    @13
    vn
    vf
    @12
    vn
    cD
    nfre1
    nfab
    nfcxfr
    nfcri
    #
    19.37
    mpbir
    @7
    @10
    vn
    @1
    @9
    vn
    @14
    @9
    vn
    nfv
    nfim
    @6
    @9
    @1
    @3
    c0
    @2
    wcel
    #
    @5
    @9
    cD
    @2
    bnj900.3
    bnj529
    @5
    @9
    @15
    @4
    @2
    c0
    eleq2
    biimparc
    sylan
    imim2i
    exlimi
    ax-mp
end
