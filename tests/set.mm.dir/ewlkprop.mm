include "cewlks.mm"
include "co.mm"
include "wcel.mm"
include "cvv.mm"
include "cxnn0.mm"
include "wa.mm"
include "cdm.mm"
include "cword.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "cfv.mm"
include "cin.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "ciedg.mm"
include "wsbc.mm"
include "cab.mm"
include "df-ewlks.mm"
include "elmpt2cl.mm"
include "simpr.mm"
include "wi.mm"
include "wb.mm"
include "isewlk.mm"
include "3expa.mm"
include "biimpd.mm"
include "expcom.mm"
include "pm2.43a.mm"
include "imp.mm"
include "3anass.mm"
include "sylanbrc.mm"
include "mpdan.mm"

theorem ewlkprop
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vs: setvar s
  let cW: class W
  assume ewlksfval.i: |- I = ( iEdg ` G )

  disjoint G k
  disjoint S k
  disjoint F k
  disjoint G f
  disjoint G g
  disjoint G i
  disjoint G s
  disjoint f g
  disjoint f i
  disjoint f k
  disjoint f s
  disjoint g i
  disjoint g k
  disjoint g s
  disjoint i k
  disjoint i s
  disjoint k s
  disjoint S f
  disjoint S g
  disjoint S i
  disjoint S s
  disjoint W f
  disjoint W g
  disjoint W k
  disjoint W s
  disjoint F f
  disjoint I f
  assert |- ( F e. ( G EdgWalks S ) -> ( ( G e. _V /\ S e. NN0* ) /\ F e. Word dom I /\ A. k e. ( 1 ..^ ( # ` F ) ) S <_ ( # ` ( ( I ` ( F ` ( k - 1 ) ) ) i^i ( I ` ( F ` k ) ) ) ) ) )

  proof
    cF
    cG
    cS
    cewlks
    co
    #
    wcel
    #
    cG
    cvv
    wcel
    #
    cS
    cxnn0
    wcel
    #
    wa
    #
    @4
    cF
    cI
    cdm
    cword
    wcel
    #
    cS
    vk
    cv
    #
    c1
    cmin
    co
    #
    cF
    cfv
    cI
    cfv
    @6
    cF
    cfv
    cI
    cfv
    cin
    chash
    cfv
    cle
    wbr
    vk
    c1
    cF
    chash
    cfv
    cfzo
    co
    wral
    #
    w3a
    #
    vg
    vs
    cvv
    cxnn0
    vf
    cv
    #
    vi
    cv
    #
    cdm
    cword
    wcel
    vs
    cv
    @7
    @10
    cfv
    @11
    cfv
    @6
    @10
    cfv
    @11
    cfv
    cin
    chash
    cfv
    cle
    wbr
    vk
    c1
    @10
    chash
    cfv
    cfzo
    co
    wral
    wa
    vi
    vg
    cv
    ciedg
    cfv
    wsbc
    vf
    cab
    cG
    cS
    cewlks
    cF
    vf
    vg
    vi
    vk
    vs
    df-ewlks
    elmpt2cl
    @1
    @4
    wa
    @4
    @5
    @8
    wa
    #
    @9
    @1
    @4
    simpr
    @1
    @4
    @12
    @4
    @1
    @12
    @4
    @1
    @1
    @12
    wi
    @4
    @1
    wa
    @1
    @12
    @2
    @3
    @1
    @1
    @12
    wb
    cS
    @0
    vk
    cF
    cG
    cI
    cvv
    ewlksfval.i
    isewlk
    3expa
    biimpd
    expcom
    pm2.43a
    imp
    @4
    @5
    @8
    3anass
    sylanbrc
    mpdan
end
