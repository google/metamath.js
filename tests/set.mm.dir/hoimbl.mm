include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "cico.mm"
include "co.mm"
include "cixp.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "cmap.mm"
include "cvoln.mm"
include "cdm.mm"
include "cfn.mm"
include "adantr.mm"
include "rrnmbl.mm"
include "csn.mm"
include "cvv.mm"
include "reex.mm"
include "mapdm0.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "a1i.mm"
include "id.mm"
include "ixpeq1d.mm"
include "ixp0x.mm"
include "eqtrd.mm"
include "oveq2.mm"
include "3eqtr4d.mm"
include "adantl.mm"
include "eleq12d.mm"
include "mpbird.mm"
include "wn.mm"
include "cmnf.mm"
include "cioo.mm"
include "cif.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "wne.mm"
include "necon3bi.mm"
include "wf.mm"
include "eqidd.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "cbvixpv.mm"
include "mpt2eq123dv.mm"
include "eqeq2.mm"
include "ixpeq2dv.mm"
include "ifeq1d.mm"
include "cbvmpt2v.mm"
include "cbvmptv.mm"
include "hoimbllem.mm"
include "pm2.61dan.mm"

theorem hoimbl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vi: setvar i
  let cX: class X
  let vl: setvar l
  let vx: setvar x
  let vy: setvar y
  let vh: setvar h
  let vj: setvar j
  let vw: setvar w
  let vz: setvar z
  let vk: setvar k
  assume hoimbl.x: |- ( ph -> X e. Fin )
  assume hoimbl.s: |- S = dom ( voln ` X )
  assume hoimbl.a: |- ( ph -> A : X --> RR )
  assume hoimbl.b: |- ( ph -> B : X --> RR )

  disjoint A i
  disjoint B i
  disjoint S i
  disjoint X i
  disjoint i ph
  disjoint A l
  disjoint A x
  disjoint A y
  disjoint i l
  disjoint i x
  disjoint i y
  disjoint l x
  disjoint l y
  disjoint x y
  disjoint B l
  disjoint B x
  disjoint B y
  disjoint X l
  disjoint X x
  disjoint X y
  disjoint h i
  disjoint h j
  disjoint h l
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint i j
  disjoint i w
  disjoint i z
  disjoint j l
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint l w
  disjoint l z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint l ph
  disjoint ph x
  disjoint ph y
  disjoint k x
  assert |- ( ph -> X_ i e. X ( ( A ` i ) [,) ( B ` i ) ) e. S )

  proof
    wph
    cX
    c0
    wceq
    #
    vi
    cX
    vi
    cv
    #
    cA
    cfv
    @1
    cB
    cfv
    cico
    co
    #
    cixp
    #
    cS
    wcel
    #
    wph
    @0
    wa
    #
    @4
    cr
    cX
    cmap
    co
    #
    cX
    cvoln
    cfv
    cdm
    #
    wcel
    @5
    cX
    wph
    cX
    cfn
    wcel
    #
    @0
    hoimbl.x
    adantr
    rrnmbl
    @5
    @3
    @6
    cS
    @7
    @0
    @3
    @6
    wceq
    wph
    @0
    c0
    csn
    #
    cr
    c0
    cmap
    co
    #
    @3
    @6
    @9
    @10
    wceq
    @0
    @10
    @9
    cr
    cvv
    wcel
    @10
    @9
    wceq
    reex
    cr
    cvv
    mapdm0
    ax-mp
    eqcomi
    a1i
    @0
    @3
    vi
    c0
    @2
    cixp
    #
    @9
    @0
    vi
    cX
    c0
    @2
    @0
    id
    #
    ixpeq1d
    @11
    @9
    wceq
    @0
    vi
    @2
    ixp0x
    a1i
    eqtrd
    cX
    c0
    cr
    cmap
    oveq2
    3eqtr4d
    adantl
    cS
    @7
    wceq
    @5
    hoimbl.s
    a1i
    eleq12d
    mpbird
    wph
    @0
    wn
    #
    wa
    vx
    vy
    cA
    cB
    cS
    vi
    vw
    cfn
    vh
    vz
    vw
    cv
    #
    cr
    vj
    @14
    vj
    cv
    #
    vh
    cv
    #
    wceq
    #
    cmnf
    vz
    cv
    #
    cioo
    co
    #
    cr
    cif
    #
    cixp
    #
    cmpt2
    #
    cmpt
    cX
    vl
    wph
    @8
    @13
    hoimbl.x
    adantr
    @13
    cX
    c0
    wne
    wph
    @0
    cX
    c0
    @12
    necon3bi
    adantl
    hoimbl.s
    wph
    cX
    cr
    cA
    wf
    @13
    hoimbl.a
    adantr
    wph
    cX
    cr
    cB
    wf
    @13
    hoimbl.b
    adantr
    vw
    vx
    cfn
    @22
    vl
    vy
    vx
    cv
    #
    cr
    vi
    @23
    @1
    vl
    cv
    #
    wceq
    #
    cmnf
    vy
    cv
    #
    cioo
    co
    #
    cr
    cif
    #
    cixp
    #
    cmpt2
    #
    @14
    @23
    wceq
    #
    @22
    vh
    vz
    @23
    cr
    vi
    @23
    @1
    @16
    wceq
    #
    @19
    cr
    cif
    #
    cixp
    #
    cmpt2
    #
    @30
    @31
    vh
    vz
    @14
    cr
    @21
    @23
    cr
    @34
    @31
    id
    #
    @31
    cr
    eqidd
    @31
    @21
    vj
    @23
    @20
    cixp
    #
    @34
    @31
    vj
    @14
    @23
    @20
    @36
    ixpeq1d
    @37
    @34
    wceq
    @31
    vj
    vi
    @23
    @20
    @33
    @15
    @1
    wceq
    @17
    @32
    @19
    cr
    @15
    @1
    @16
    eqeq1
    ifbid
    cbvixpv
    a1i
    eqtrd
    mpt2eq123dv
    @35
    @30
    wceq
    @31
    vh
    vz
    vl
    vy
    @23
    cr
    @34
    @29
    vi
    @23
    @25
    @19
    cr
    cif
    #
    cixp
    @16
    @24
    wceq
    #
    vi
    @23
    @33
    @38
    @39
    @32
    @25
    @19
    cr
    @16
    @24
    @1
    eqeq2
    ifbid
    ixpeq2dv
    @18
    @26
    wceq
    #
    vi
    @23
    @38
    @28
    @40
    @25
    @19
    @27
    cr
    @18
    @26
    cmnf
    cioo
    oveq2
    ifeq1d
    ixpeq2dv
    cbvmpt2v
    a1i
    eqtrd
    cbvmptv
    hoimbllem
    pm2.61dan
end
