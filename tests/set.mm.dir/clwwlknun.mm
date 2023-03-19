include "cusgr.mm"
include "wcel.mm"
include "cclwwlkn.mm"
include "co.mm"
include "cv.mm"
include "cclwwlknon.mm"
include "cfv.mm"
include "ciun.mm"
include "wrex.mm"
include "eliun.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "isclwwlknon.mm"
include "rexbii.mm"
include "simpl.mm"
include "rexlimivw.mm"
include "cword.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "cedg.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "clsw.mm"
include "w3a.mm"
include "eqid.mm"
include "clwwlknp.mm"
include "anim2i.mm"
include "wi.mm"
include "usgrpredgv.mm"
include "ex.mm"
include "simpr.mm"
include "syl6com.mm"
include "3ad2ant3.mm"
include "impcom.mm"
include "eqcomd.mm"
include "biantrud.mm"
include "bicomd.mm"
include "rspcedv.mm"
include "adantld.mm"
include "mpcom.mm"
include "impbid2.mm"
include "syl5bb.mm"
include "syl5rbb.mm"
include "eqrdv.mm"

theorem clwwlknun
  let vx: setvar x
  let cG: class G
  let cN: class N
  let cV: class V
  let vw: setvar w
  let vy: setvar y
  let vi: setvar i
  assume clwwlknun.v: |- V = ( Vtx ` G )

  disjoint G x
  disjoint N x
  disjoint V x
  disjoint G w
  disjoint G y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint N w
  disjoint N y
  disjoint V y
  disjoint G i
  disjoint i x
  disjoint i y
  disjoint N i
  assert |- ( G e. USGraph -> ( N ClWWalksN G ) = U_ x e. V ( x ( ClWWalksNOn ` G ) N ) )

  proof
    cG
    cusgr
    wcel
    #
    vy
    cN
    cG
    cclwwlkn
    co
    #
    vx
    cV
    vx
    cv
    #
    cN
    cG
    cclwwlknon
    cfv
    co
    #
    ciun
    #
    vy
    cv
    #
    @4
    wcel
    @5
    @3
    wcel
    #
    vx
    cV
    wrex
    #
    @0
    @5
    @1
    wcel
    #
    vx
    @5
    cV
    @3
    eliun
    @7
    @8
    cc0
    @5
    cfv
    #
    @2
    wceq
    #
    wa
    #
    vx
    cV
    wrex
    #
    @0
    @8
    @6
    @11
    vx
    cV
    cG
    cN
    @5
    @2
    isclwwlknon
    rexbii
    @0
    @12
    @8
    @11
    @8
    vx
    cV
    @8
    @10
    simpl
    rexlimivw
    @0
    @8
    @12
    @0
    @5
    cV
    cword
    wcel
    @5
    chash
    cfv
    cN
    wceq
    wa
    #
    vi
    cv
    #
    @5
    cfv
    @14
    c1
    caddc
    co
    @5
    cfv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    vi
    cc0
    cN
    c1
    cmin
    co
    cfzo
    co
    wral
    #
    @5
    clsw
    cfv
    #
    @9
    cpr
    @15
    wcel
    #
    w3a
    #
    wa
    #
    @0
    @8
    wa
    @12
    @8
    @19
    @0
    vi
    @15
    cG
    cN
    cV
    @5
    clwwlknun.v
    @15
    eqid
    #
    clwwlknp
    anim2i
    @20
    @8
    @12
    @0
    @20
    @11
    @8
    vx
    @9
    cV
    @19
    @0
    @9
    cV
    wcel
    #
    @18
    @13
    @0
    @22
    wi
    @16
    @0
    @18
    @17
    cV
    wcel
    #
    @22
    wa
    #
    @22
    @0
    @18
    @24
    @15
    cG
    @17
    @9
    cV
    @21
    clwwlknun.v
    usgrpredgv
    ex
    @23
    @22
    simpr
    syl6com
    3ad2ant3
    impcom
    @20
    @2
    @9
    wceq
    #
    wa
    #
    @8
    @11
    @26
    @10
    @8
    @26
    @2
    @9
    @20
    @25
    simpr
    eqcomd
    biantrud
    bicomd
    rspcedv
    adantld
    mpcom
    ex
    impbid2
    syl5bb
    syl5rbb
    eqrdv
end
