include "cfv.mm"
include "ccnv.mm"
include "c0g.mm"
include "csn.mm"
include "cima.mm"
include "wcel.mm"
include "cbs.mm"
include "wceq.mm"
include "cz.mm"
include "zring.mm"
include "crh.mm"
include "co.mm"
include "wf.mm"
include "crg.mm"
include "ccrg.mm"
include "cidom.mm"
include "cfield.mm"
include "cprime.mm"
include "c2.mm"
include "eldifad.mm"
include "znfld.mm"
include "syl.mm"
include "fldidom.mm"
include "cdomn.mm"
include "isidom.mm"
include "simplbi.mm"
include "crngring.mm"
include "zrhrhm.mm"
include "zringbas.mm"
include "eqid.mm"
include "rhmf.mm"
include "ffvelrnd.mm"
include "clgs.mm"
include "cmo.mm"
include "c1.mm"
include "cmin.mm"
include "cdiv.mm"
include "cexp.mm"
include "cdif.mm"
include "lgsvalmod.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "lgsqrlem1.mm"
include "wfn.mm"
include "wa.mm"
include "wb.mm"
include "cpws.mm"
include "cvv.mm"
include "fvexd.mm"
include "evl1rhm.mm"
include "cgrp.mm"
include "ply1ring.mm"
include "ringgrp.mm"
include "cmgp.mm"
include "cmnd.mm"
include "cn0.mm"
include "ringmgp.mm"
include "cn.mm"
include "oddprm.mm"
include "nnnn0d.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "ringidcl.mm"
include "grpsubcl.mm"
include "syl5eqel.mm"
include "pwselbas.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mpbir2and.mm"

theorem lgsqrlem3
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cS: class S
  let cT: class T
  let c.1: class .1.
  let c.ex: class .^
  let cG: class G
  let cL: class L
  let c.mi: class .-
  let cO: class O
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vz: setvar z
  assume lgsqr.y: |- Y = ( Z/nZ ` P )
  assume lgsqr.s: |- S = ( Poly1 ` Y )
  assume lgsqr.b: |- B = ( Base ` S )
  assume lgsqr.d: |- D = ( deg1 ` Y )
  assume lgsqr.o: |- O = ( eval1 ` Y )
  assume lgsqr.e: |- .^ = ( .g ` ( mulGrp ` S ) )
  assume lgsqr.x: |- X = ( var1 ` Y )
  assume lgsqr.m: |- .- = ( -g ` S )
  assume lgsqr.u: |- .1. = ( 1r ` S )
  assume lgsqr.t: |- T = ( ( ( ( P - 1 ) / 2 ) .^ X ) .- .1. )
  assume lgsqr.l: |- L = ( ZRHom ` Y )
  assume lgsqr.1: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume lgsqr.g: |- G = ( y e. ( 1 ... ( ( P - 1 ) / 2 ) ) |-> ( L ` ( y ^ 2 ) ) )
  assume lgsqr.3: |- ( ph -> A e. ZZ )
  assume lgsqr.4: |- ( ph -> ( A /L P ) = 1 )

  disjoint O y
  disjoint P y
  disjoint ph y
  disjoint T y
  disjoint L y
  disjoint Y y
  disjoint A x
  disjoint x z
  disjoint G x
  disjoint G z
  disjoint x y
  disjoint P x
  disjoint y z
  disjoint P z
  disjoint ph x
  disjoint ph z
  disjoint L x
  disjoint Y x
  assert |- ( ph -> ( L ` A ) e. ( `' ( O ` T ) " { ( 0g ` Y ) } ) )

  proof
    wph
    cA
    cL
    cfv
    #
    cT
    cO
    cfv
    #
    ccnv
    cY
    c0g
    cfv
    #
    csn
    cima
    wcel
    #
    @0
    cY
    cbs
    cfv
    #
    wcel
    #
    @0
    @1
    cfv
    @2
    wceq
    #
    wph
    cz
    @4
    cA
    cL
    wph
    cL
    zring
    cY
    crh
    co
    wcel
    #
    cz
    @4
    cL
    wf
    wph
    cY
    crg
    wcel
    #
    @7
    wph
    cY
    ccrg
    wcel
    #
    @8
    wph
    cY
    cidom
    wcel
    #
    @9
    wph
    cY
    cfield
    wcel
    #
    @10
    wph
    cP
    cprime
    wcel
    @11
    wph
    cP
    cprime
    c2
    csn
    #
    lgsqr.1
    eldifad
    cP
    cY
    lgsqr.y
    znfld
    syl
    #
    cY
    fldidom
    syl
    @10
    @9
    cY
    cdomn
    wcel
    cY
    isidom
    simplbi
    syl
    #
    cY
    crngring
    syl
    #
    cY
    cL
    lgsqr.l
    zrhrhm
    syl
    cz
    @4
    zring
    cY
    cL
    zringbas
    @4
    eqid
    #
    rhmf
    syl
    lgsqr.3
    ffvelrnd
    wph
    cA
    cB
    cD
    cP
    cS
    cT
    c.1
    c.ex
    cL
    c.mi
    cO
    cX
    cY
    lgsqr.y
    lgsqr.s
    lgsqr.b
    lgsqr.d
    lgsqr.o
    lgsqr.e
    lgsqr.x
    lgsqr.m
    lgsqr.u
    lgsqr.t
    lgsqr.l
    lgsqr.1
    lgsqr.3
    wph
    cA
    cP
    clgs
    co
    #
    cP
    cmo
    co
    #
    cA
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cexp
    co
    cP
    cmo
    co
    #
    c1
    cP
    cmo
    co
    wph
    cA
    cz
    wcel
    cP
    cprime
    @12
    cdif
    wcel
    #
    @18
    @20
    wceq
    lgsqr.3
    lgsqr.1
    cA
    cP
    lgsvalmod
    syl2anc
    wph
    @17
    c1
    cP
    cmo
    lgsqr.4
    oveq1d
    eqtr3d
    lgsqrlem1
    wph
    @1
    @4
    wfn
    #
    @3
    @5
    @6
    wa
    wb
    wph
    @4
    @4
    @1
    wf
    @22
    wph
    @4
    cY
    @4
    cY
    @4
    cpws
    co
    #
    cbs
    cfv
    #
    cfield
    @1
    @23
    cvv
    @23
    eqid
    #
    @16
    @24
    eqid
    #
    @13
    wph
    cY
    cbs
    fvexd
    wph
    cB
    @24
    cT
    cO
    wph
    cO
    cS
    @23
    crh
    co
    wcel
    #
    cB
    @24
    cO
    wf
    wph
    @9
    @27
    @14
    @4
    cS
    cY
    @23
    cO
    lgsqr.o
    lgsqr.s
    @25
    @16
    evl1rhm
    syl
    cB
    @24
    cS
    @23
    cO
    lgsqr.b
    @26
    rhmf
    syl
    wph
    cT
    @19
    cX
    c.ex
    co
    #
    c.1
    c.mi
    co
    #
    cB
    lgsqr.t
    wph
    cS
    cgrp
    wcel
    #
    @28
    cB
    wcel
    #
    c.1
    cB
    wcel
    #
    @29
    cB
    wcel
    wph
    cS
    crg
    wcel
    #
    @30
    wph
    @8
    @33
    @15
    cS
    cY
    lgsqr.s
    ply1ring
    syl
    #
    cS
    ringgrp
    syl
    wph
    cS
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @19
    cn0
    wcel
    cX
    cB
    wcel
    #
    @31
    wph
    @33
    @36
    @34
    cS
    @35
    @35
    eqid
    #
    ringmgp
    syl
    wph
    @19
    wph
    @21
    @19
    cn
    wcel
    lgsqr.1
    cP
    oddprm
    syl
    nnnn0d
    wph
    @8
    @37
    @15
    cB
    cS
    cY
    cX
    lgsqr.x
    lgsqr.s
    lgsqr.b
    vr1cl
    syl
    cB
    c.ex
    @35
    @19
    cX
    cB
    cS
    @35
    @38
    lgsqr.b
    mgpbas
    lgsqr.e
    mulgnn0cl
    syl3anc
    wph
    @33
    @32
    @34
    cB
    cS
    c.1
    lgsqr.b
    lgsqr.u
    ringidcl
    syl
    cB
    cS
    c.mi
    @28
    c.1
    lgsqr.b
    lgsqr.m
    grpsubcl
    syl3anc
    syl5eqel
    ffvelrnd
    pwselbas
    @4
    @4
    @1
    ffn
    syl
    @4
    @2
    @0
    @1
    fniniseg
    syl
    mpbir2and
end
