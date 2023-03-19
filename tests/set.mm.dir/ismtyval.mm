include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "cuni.mm"
include "cv.mm"
include "cdm.mm"
include "wf1o.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cab.mm"
include "cismty.mm"
include "cvv.mm"
include "cmpt2.mm"
include "df-ismty.mm"
include "a1i.mm"
include "wb.mm"
include "cxp.mm"
include "dmeq.mm"
include "cxr.mm"
include "wf.mm"
include "xmetf.mm"
include "fdm.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "ad2ant2r.mm"
include "dmeqd.mm"
include "dmxpid.mm"
include "syl6eq.mm"
include "f1oeq2.mm"
include "ad2ant2l.mm"
include "f1oeq3.mm"
include "bitrd.mm"
include "oveq.mm"
include "eqeqan12d.mm"
include "adantl.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "abbidv.mm"
include "fvssunirn.mm"
include "simpl.mm"
include "sseldi.mm"
include "simpr.mm"
include "cmap.mm"
include "wss.mm"
include "f1of.mm"
include "adantr.mm"
include "elfvdm.mm"
include "elmapg.mm"
include "syl2anr.mm"
include "syl5ibr.mm"
include "abssdv.mm"
include "ovex.mm"
include "ssex.mm"
include "ovmpt2d.mm"

theorem ismtyval
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vm: setvar m
  let vn: setvar n

  disjoint M f
  disjoint M x
  disjoint M y
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint N f
  disjoint N x
  disjoint N y
  disjoint X f
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y x
  disjoint Y y
  disjoint M m
  disjoint M n
  disjoint m n
  disjoint f m
  disjoint m x
  disjoint m y
  disjoint f n
  disjoint n x
  disjoint n y
  disjoint N m
  disjoint N n
  disjoint X m
  disjoint X n
  disjoint Y m
  disjoint Y n
  assert |- ( ( M e. ( *Met ` X ) /\ N e. ( *Met ` Y ) ) -> ( M Ismty N ) = { f | ( f : X -1-1-onto-> Y /\ A. x e. X A. y e. X ( x M y ) = ( ( f ` x ) N ( f ` y ) ) ) } )

  proof
    cM
    cX
    cxmt
    cfv
    #
    wcel
    #
    cN
    cY
    cxmt
    cfv
    #
    wcel
    #
    wa
    #
    vm
    vn
    cM
    cN
    cxmt
    crn
    cuni
    #
    @5
    vm
    cv
    #
    cdm
    #
    cdm
    #
    vn
    cv
    #
    cdm
    #
    cdm
    #
    vf
    cv
    #
    wf1o
    #
    vx
    cv
    #
    vy
    cv
    #
    @6
    co
    #
    @14
    @12
    cfv
    #
    @15
    @12
    cfv
    #
    @9
    co
    #
    wceq
    #
    vy
    @8
    wral
    #
    vx
    @8
    wral
    #
    wa
    #
    vf
    cab
    #
    cX
    cY
    @12
    wf1o
    #
    @14
    @15
    cM
    co
    #
    @17
    @18
    cN
    co
    #
    wceq
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    wa
    #
    vf
    cab
    #
    cismty
    cvv
    cismty
    vm
    vn
    @5
    @5
    @24
    cmpt2
    wceq
    @4
    vx
    vy
    vf
    vm
    vn
    df-ismty
    a1i
    @4
    @6
    cM
    wceq
    #
    @9
    cN
    wceq
    #
    wa
    #
    wa
    #
    @23
    @31
    vf
    @36
    @13
    @25
    @22
    @30
    @36
    @13
    cX
    @11
    @12
    wf1o
    #
    @25
    @36
    @8
    cX
    wceq
    @13
    @37
    wb
    @36
    @8
    cX
    cX
    cxp
    #
    cdm
    cX
    @36
    @7
    @38
    @1
    @33
    @7
    @38
    wceq
    @3
    @34
    @33
    @1
    @7
    cM
    cdm
    #
    @38
    @6
    cM
    dmeq
    @1
    @38
    cxr
    cM
    wf
    @39
    @38
    wceq
    cM
    cX
    xmetf
    @38
    cxr
    cM
    fdm
    syl
    sylan9eqr
    ad2ant2r
    dmeqd
    cX
    dmxpid
    syl6eq
    #
    @8
    cX
    @11
    @12
    f1oeq2
    syl
    @36
    @11
    cY
    wceq
    @37
    @25
    wb
    @36
    @11
    cY
    cY
    cxp
    #
    cdm
    cY
    @36
    @10
    @41
    @3
    @34
    @10
    @41
    wceq
    @1
    @33
    @34
    @3
    @10
    cN
    cdm
    #
    @41
    @9
    cN
    dmeq
    @3
    @41
    cxr
    cN
    wf
    @42
    @41
    wceq
    cN
    cY
    xmetf
    @41
    cxr
    cN
    fdm
    syl
    sylan9eqr
    ad2ant2l
    dmeqd
    cY
    dmxpid
    syl6eq
    @11
    cY
    cX
    @12
    f1oeq3
    syl
    bitrd
    @36
    @21
    @29
    vx
    @8
    cX
    @40
    @36
    @20
    @28
    vy
    @8
    cX
    @40
    @35
    @20
    @28
    wb
    @4
    @33
    @34
    @16
    @26
    @19
    @27
    @14
    @15
    @6
    cM
    oveq
    @17
    @18
    @9
    cN
    oveq
    eqeqan12d
    adantl
    raleqbidv
    raleqbidv
    anbi12d
    abbidv
    @4
    @0
    @5
    cM
    cxmt
    cX
    fvssunirn
    @1
    @3
    simpl
    sseldi
    @4
    @2
    @5
    cN
    cxmt
    cY
    fvssunirn
    @1
    @3
    simpr
    sseldi
    @4
    @32
    cY
    cX
    cmap
    co
    #
    wss
    @32
    cvv
    wcel
    @4
    @31
    vf
    @43
    @31
    @12
    @43
    wcel
    #
    @4
    cX
    cY
    @12
    wf
    #
    @25
    @45
    @30
    cX
    cY
    @12
    f1of
    adantr
    @3
    cY
    cxmt
    cdm
    #
    wcel
    cX
    @46
    wcel
    @44
    @45
    wb
    @1
    cN
    cY
    cxmt
    elfvdm
    cM
    cX
    cxmt
    elfvdm
    cY
    cX
    @12
    @46
    @46
    elmapg
    syl2anr
    syl5ibr
    abssdv
    @32
    @43
    cY
    cX
    cmap
    ovex
    ssex
    syl
    ovmpt2d
end
