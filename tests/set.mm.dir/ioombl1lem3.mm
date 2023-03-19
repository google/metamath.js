include "cv.mm"
include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cabs.mm"
include "ccom.mm"
include "cfv.mm"
include "c2nd.mm"
include "cr.mm"
include "c1st.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "w3a.mm"
include "ovolfcl.mm"
include "sylan.mm"
include "simp2d.mm"
include "syl5eqel.mm"
include "recnd.mm"
include "adantr.mm"
include "simp1d.mm"
include "ifcld.mm"
include "npncand.mm"
include "wceq.mm"
include "ioombl1lem1.mm"
include "simpld.mm"
include "eqid.mm"
include "ovolfsval.mm"
include "cop.mm"
include "cvv.mm"
include "simpr.mm"
include "opex.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "op2ndg.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "op1stg.mm"
include "oveq12d.mm"
include "simprd.mm"
include "oveq12i.mm"
include "syl6eqr.mm"
include "3eqtr4d.mm"

theorem ioombl1lem3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cU: class U
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let vz: setvar z
  assume ioombl1.b: |- B = ( A (,) +oo )
  assume ioombl1.a: |- ( ph -> A e. RR )
  assume ioombl1.e: |- ( ph -> E C_ RR )
  assume ioombl1.v: |- ( ph -> ( vol* ` E ) e. RR )
  assume ioombl1.c: |- ( ph -> C e. RR+ )
  assume ioombl1.s: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )
  assume ioombl1.t: |- T = seq 1 ( + , ( ( abs o. - ) o. G ) )
  assume ioombl1.u: |- U = seq 1 ( + , ( ( abs o. - ) o. H ) )
  assume ioombl1.f1: |- ( ph -> F : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume ioombl1.f2: |- ( ph -> E C_ U. ran ( (,) o. F ) )
  assume ioombl1.f3: |- ( ph -> sup ( ran S , RR* , < ) <_ ( ( vol* ` E ) + C ) )
  assume ioombl1.p: |- P = ( 1st ` ( F ` n ) )
  assume ioombl1.q: |- Q = ( 2nd ` ( F ` n ) )
  assume ioombl1.g: |- G = ( n e. NN |-> <. if ( if ( P <_ A , A , P ) <_ Q , if ( P <_ A , A , P ) , Q ) , Q >. )
  assume ioombl1.h: |- H = ( n e. NN |-> <. P , if ( if ( P <_ A , A , P ) <_ Q , if ( P <_ A , A , P ) , Q ) >. )

  disjoint B n
  disjoint C n
  disjoint E n
  disjoint F n
  disjoint G n
  disjoint H n
  disjoint n ph
  disjoint S n
  disjoint n x
  disjoint B x
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint C j
  disjoint k n
  disjoint k x
  disjoint C k
  disjoint C x
  disjoint E x
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint G j
  disjoint G k
  disjoint G x
  disjoint H j
  disjoint H k
  disjoint H x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint j z
  disjoint S j
  disjoint k z
  disjoint S k
  disjoint n z
  disjoint x z
  disjoint S x
  disjoint S z
  disjoint T j
  disjoint T x
  disjoint T z
  disjoint U j
  disjoint U x
  disjoint U z
  assert |- ( ( ph /\ n e. NN ) -> ( ( ( ( abs o. - ) o. G ) ` n ) + ( ( ( abs o. - ) o. H ) ` n ) ) = ( ( ( abs o. - ) o. F ) ` n ) )

  proof
    wph
    vn
    cv
    #
    cn
    wcel
    #
    wa
    #
    cQ
    cP
    cA
    cle
    wbr
    #
    cA
    cP
    cif
    #
    cQ
    cle
    wbr
    #
    @4
    cQ
    cif
    #
    cmin
    co
    #
    @6
    cP
    cmin
    co
    #
    caddc
    co
    cQ
    cP
    cmin
    co
    #
    @0
    cabs
    cmin
    ccom
    #
    cG
    ccom
    #
    cfv
    #
    @0
    @10
    cH
    ccom
    #
    cfv
    #
    caddc
    co
    @0
    @10
    cF
    ccom
    #
    cfv
    #
    @2
    cQ
    @6
    cP
    @2
    cQ
    @2
    cQ
    @0
    cF
    cfv
    #
    c2nd
    cfv
    #
    cr
    ioombl1.q
    @2
    @17
    c1st
    cfv
    #
    cr
    wcel
    #
    @18
    cr
    wcel
    #
    @19
    @18
    cle
    wbr
    #
    wph
    cn
    cle
    cr
    cr
    cxp
    cin
    #
    cF
    wf
    #
    @1
    @20
    @21
    @22
    w3a
    ioombl1.f1
    cF
    @0
    ovolfcl
    sylan
    #
    simp2d
    syl5eqel
    #
    recnd
    @2
    @6
    @2
    @5
    @4
    cQ
    cr
    @2
    @3
    cA
    cP
    cr
    wph
    cA
    cr
    wcel
    @1
    ioombl1.a
    adantr
    @2
    cP
    @19
    cr
    ioombl1.p
    @2
    @20
    @21
    @22
    @25
    simp1d
    syl5eqel
    #
    ifcld
    @26
    ifcld
    #
    recnd
    @2
    cP
    @27
    recnd
    npncand
    @2
    @12
    @7
    @14
    @8
    caddc
    @2
    @12
    @0
    cG
    cfv
    #
    c2nd
    cfv
    #
    @29
    c1st
    cfv
    #
    cmin
    co
    #
    @7
    wph
    cn
    @23
    cG
    wf
    #
    @1
    @12
    @32
    wceq
    wph
    @33
    cn
    @23
    cH
    wf
    #
    wph
    cA
    cB
    cC
    cP
    cQ
    cS
    cT
    cU
    vn
    cE
    cF
    cG
    cH
    ioombl1.b
    ioombl1.a
    ioombl1.e
    ioombl1.v
    ioombl1.c
    ioombl1.s
    ioombl1.t
    ioombl1.u
    ioombl1.f1
    ioombl1.f2
    ioombl1.f3
    ioombl1.p
    ioombl1.q
    ioombl1.g
    ioombl1.h
    ioombl1lem1
    #
    simpld
    cG
    @11
    @0
    @11
    eqid
    ovolfsval
    sylan
    @2
    @30
    cQ
    @31
    @6
    cmin
    @2
    @30
    @6
    cQ
    cop
    #
    c2nd
    cfv
    #
    cQ
    @2
    @29
    @36
    c2nd
    @2
    @1
    @36
    cvv
    wcel
    @29
    @36
    wceq
    wph
    @1
    simpr
    #
    @6
    cQ
    opex
    vn
    cn
    @36
    cvv
    cG
    ioombl1.g
    fvmpt2
    sylancl
    #
    fveq2d
    @2
    @6
    cr
    wcel
    #
    cQ
    cr
    wcel
    #
    @37
    cQ
    wceq
    @28
    @26
    @6
    cQ
    cr
    cr
    op2ndg
    syl2anc
    eqtrd
    @2
    @31
    @36
    c1st
    cfv
    #
    @6
    @2
    @29
    @36
    c1st
    @39
    fveq2d
    @2
    @40
    @41
    @42
    @6
    wceq
    @28
    @26
    @6
    cQ
    cr
    cr
    op1stg
    syl2anc
    eqtrd
    oveq12d
    eqtrd
    @2
    @14
    @0
    cH
    cfv
    #
    c2nd
    cfv
    #
    @43
    c1st
    cfv
    #
    cmin
    co
    #
    @8
    wph
    @34
    @1
    @14
    @46
    wceq
    wph
    @33
    @34
    @35
    simprd
    cH
    @13
    @0
    @13
    eqid
    ovolfsval
    sylan
    @2
    @44
    @6
    @45
    cP
    cmin
    @2
    @44
    cP
    @6
    cop
    #
    c2nd
    cfv
    #
    @6
    @2
    @43
    @47
    c2nd
    @2
    @1
    @47
    cvv
    wcel
    @43
    @47
    wceq
    @38
    cP
    @6
    opex
    vn
    cn
    @47
    cvv
    cH
    ioombl1.h
    fvmpt2
    sylancl
    #
    fveq2d
    @2
    cP
    cr
    wcel
    #
    @40
    @48
    @6
    wceq
    @27
    @28
    cP
    @6
    cr
    cr
    op2ndg
    syl2anc
    eqtrd
    @2
    @45
    @47
    c1st
    cfv
    #
    cP
    @2
    @43
    @47
    c1st
    @49
    fveq2d
    @2
    @50
    @40
    @51
    cP
    wceq
    @27
    @28
    cP
    @6
    cr
    cr
    op1stg
    syl2anc
    eqtrd
    oveq12d
    eqtrd
    oveq12d
    @2
    @16
    @18
    @19
    cmin
    co
    #
    @9
    wph
    @24
    @1
    @16
    @52
    wceq
    ioombl1.f1
    cF
    @15
    @0
    @15
    eqid
    ovolfsval
    sylan
    cQ
    @18
    cP
    @19
    cmin
    ioombl1.q
    ioombl1.p
    oveq12i
    syl6eqr
    3eqtr4d
end
