include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cn.mm"
include "wa.mm"
include "cgcd.mm"
include "c1.mm"
include "eqcom.mm"
include "cdiv.mm"
include "cn0.mm"
include "simpl2.mm"
include "odcl.mm"
include "syl.mm"
include "nn0cnd.mm"
include "simpl1.mm"
include "simpl3.mm"
include "mulgcl.mm"
include "syl3anc.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "adantl.mm"
include "cdvds.mm"
include "wbr.mm"
include "odmulg2.mm"
include "adantr.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "wb.mm"
include "nn0zd.mm"
include "0dvds.mm"
include "sylibd.mm"
include "necon3d.mm"
include "mpd.mm"
include "diveq1ad.mm"
include "cmul.mm"
include "gcdcld.mm"
include "mulcomd.mm"
include "odmulg.mm"
include "eqtr4d.mm"
include "divmuld.mm"
include "mpbird.mm"
include "eqeq1d.mm"
include "bitr3d.mm"
include "syl5bb.mm"

theorem odmulgeq
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cO: class O
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume odmulgid.1: |- X = ( Base ` G )
  assume odmulgid.2: |- O = ( od ` G )
  assume odmulgid.3: |- .x. = ( .g ` G )


  assert |- ( ( ( G e. Grp /\ A e. X /\ N e. ZZ ) /\ ( O ` A ) e. NN ) -> ( ( O ` ( N .x. A ) ) = ( O ` A ) <-> ( N gcd ( O ` A ) ) = 1 ) )

  proof
    cN
    cA
    c.x
    co
    #
    cO
    cfv
    #
    cA
    cO
    cfv
    #
    wceq
    @2
    @1
    wceq
    #
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    @2
    cn
    wcel
    #
    wa
    #
    cN
    @2
    cgcd
    co
    #
    c1
    wceq
    #
    @1
    @2
    eqcom
    @9
    @2
    @1
    cdiv
    co
    #
    c1
    wceq
    @3
    @11
    @9
    @2
    @1
    @9
    @2
    @9
    @5
    @2
    cn0
    wcel
    @4
    @5
    @6
    @8
    simpl2
    #
    cA
    cG
    cO
    cX
    odmulgid.1
    odmulgid.2
    odcl
    syl
    #
    nn0cnd
    #
    @9
    @1
    @9
    @0
    cX
    wcel
    #
    @1
    cn0
    wcel
    @9
    @4
    @6
    @5
    @16
    @4
    @5
    @6
    @8
    simpl1
    @4
    @5
    @6
    @8
    simpl3
    #
    @13
    cX
    c.x
    cG
    cN
    cA
    odmulgid.1
    odmulgid.3
    mulgcl
    syl3anc
    @0
    cG
    cO
    cX
    odmulgid.1
    odmulgid.2
    odcl
    syl
    nn0cnd
    #
    @9
    @2
    cc0
    wne
    #
    @1
    cc0
    wne
    @8
    @19
    @7
    @2
    nnne0
    adantl
    @9
    @1
    cc0
    @2
    cc0
    @9
    @1
    cc0
    wceq
    #
    cc0
    @2
    cdvds
    wbr
    #
    @2
    cc0
    wceq
    #
    @9
    @1
    @2
    cdvds
    wbr
    #
    @20
    @21
    @7
    @23
    @8
    cA
    c.x
    cG
    cN
    cO
    cX
    odmulgid.1
    odmulgid.2
    odmulgid.3
    odmulg2
    adantr
    @1
    cc0
    @2
    cdvds
    breq1
    syl5ibcom
    @9
    @2
    cz
    wcel
    @21
    @22
    wb
    @9
    @2
    @14
    nn0zd
    #
    @2
    0dvds
    syl
    sylibd
    necon3d
    mpd
    #
    diveq1ad
    @9
    @12
    @10
    c1
    @9
    @12
    @10
    wceq
    @1
    @10
    cmul
    co
    #
    @2
    wceq
    @9
    @26
    @10
    @1
    cmul
    co
    #
    @2
    @9
    @1
    @10
    @18
    @9
    @10
    @9
    cN
    @2
    @17
    @24
    gcdcld
    nn0cnd
    #
    mulcomd
    @7
    @2
    @27
    wceq
    @8
    cA
    c.x
    cG
    cN
    cO
    cX
    odmulgid.1
    odmulgid.2
    odmulgid.3
    odmulg
    adantr
    eqtr4d
    @9
    @2
    @1
    @10
    @15
    @18
    @28
    @25
    divmuld
    mpbird
    eqeq1d
    bitr3d
    syl5bb
end
