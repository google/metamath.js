include "w-bnj17.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "wss.mm"
include "wex.mm"
include "19.8a.mm"
include "bnj707.mm"
include "bnj1083.mm"
include "sylibr.mm"
include "simplbi.mm"
include "bnj708.mm"
include "wfn.mm"
include "wceq.mm"
include "bnj1235.mm"
include "fndm.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "wa.mm"
include "wi.mm"
include "bnj1294.mm"
include "sylib.mm"
include "mp2and.mm"
include "simprbi.mm"
include "sseldd.mm"

theorem bnj1121
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cK: class K
  let cX: class X
  assume bnj1121.1: |- ( th <-> ( R _FrSe A /\ X e. A ) )
  assume bnj1121.2: |- ( ta <-> ( B e. _V /\ _TrFo ( B , A , R ) /\ _pred ( X , A , R ) C_ B ) )
  assume bnj1121.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1121.4: |- ( ze <-> ( i e. n /\ z e. ( f ` i ) ) )
  assume bnj1121.5: |- ( et <-> ( ( f e. K /\ i e. dom f ) -> ( f ` i ) C_ B ) )
  assume bnj1121.6: |- ( ( th /\ ta /\ ch /\ ze ) -> A. i e. n et )
  assume bnj1121.7: |- K = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }


  assert |- ( ( th /\ ta /\ ch /\ ze ) -> z e. B )

  proof
    wth
    wta
    wch
    wze
    w-bnj17
    #
    vi
    cv
    #
    vf
    cv
    #
    cfv
    #
    cB
    vz
    cv
    #
    @0
    @2
    cK
    wcel
    #
    @1
    @2
    cdm
    #
    wcel
    #
    @3
    cB
    wss
    #
    @0
    wch
    vn
    wex
    #
    @5
    wth
    wta
    wch
    wze
    @9
    wch
    vn
    19.8a
    bnj707
    wph
    wps
    wch
    cD
    vf
    vn
    cK
    bnj1121.3
    bnj1121.7
    bnj1083
    sylibr
    @0
    @1
    vn
    cv
    #
    @6
    wth
    wta
    wch
    wze
    @1
    @10
    wcel
    #
    wze
    @11
    @4
    @3
    wcel
    #
    bnj1121.4
    simplbi
    bnj708
    #
    @0
    @2
    @10
    wfn
    #
    @6
    @10
    wceq
    wth
    wta
    wch
    wze
    @14
    wch
    @10
    cD
    wcel
    @14
    wph
    wps
    bnj1121.3
    bnj1235
    bnj707
    @10
    @2
    fndm
    syl
    eleqtrrd
    @0
    wet
    @5
    @7
    wa
    @8
    wi
    @0
    wet
    vi
    @10
    bnj1121.6
    @13
    bnj1294
    bnj1121.5
    sylib
    mp2and
    wth
    wta
    wch
    wze
    @12
    wze
    @11
    @12
    bnj1121.4
    simprbi
    bnj708
    sseldd
end
