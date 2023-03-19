include "cn.mm"
include "cle.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "wbr.mm"
include "cif.mm"
include "cop.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "adantr.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "w3a.mm"
include "ovolfcl.mm"
include "sylan.mm"
include "simp1d.mm"
include "syl5eqel.mm"
include "ifcld.mm"
include "simp2d.mm"
include "min2.mm"
include "syl2anc.mm"
include "df-br.mm"
include "sylib.mm"
include "opelxpi.mm"
include "elind.mm"
include "fmptd.mm"
include "max1.mm"
include "simp3d.mm"
include "3brtr4g.mm"
include "breq2.mm"
include "ifboth.mm"
include "jca.mm"

theorem ioombl1lem1
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
  assert |- ( ph -> ( G : NN --> ( <_ i^i ( RR X. RR ) ) /\ H : NN --> ( <_ i^i ( RR X. RR ) ) ) )

  proof
    wph
    cn
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cG
    wf
    cn
    @1
    cH
    wf
    wph
    vn
    cn
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
    @3
    cQ
    cif
    #
    cQ
    cop
    #
    @1
    cG
    wph
    vn
    cv
    #
    cn
    wcel
    #
    wa
    #
    cle
    @0
    @6
    @9
    @5
    cQ
    cle
    wbr
    #
    @6
    cle
    wcel
    @9
    @3
    cr
    wcel
    cQ
    cr
    wcel
    #
    @10
    @9
    @2
    cA
    cP
    cr
    wph
    cA
    cr
    wcel
    #
    @8
    ioombl1.a
    adantr
    #
    @9
    cP
    @7
    cF
    cfv
    #
    c1st
    cfv
    #
    cr
    ioombl1.p
    @9
    @15
    cr
    wcel
    #
    @14
    c2nd
    cfv
    #
    cr
    wcel
    #
    @15
    @17
    cle
    wbr
    #
    wph
    cn
    @1
    cF
    wf
    @8
    @16
    @18
    @19
    w3a
    ioombl1.f1
    cF
    @7
    ovolfcl
    sylan
    #
    simp1d
    syl5eqel
    #
    ifcld
    #
    @9
    cQ
    @17
    cr
    ioombl1.q
    @9
    @16
    @18
    @19
    @20
    simp2d
    syl5eqel
    #
    @3
    cQ
    min2
    syl2anc
    @5
    cQ
    cle
    df-br
    sylib
    @9
    @5
    cr
    wcel
    #
    @11
    @6
    @0
    wcel
    @9
    @4
    @3
    cQ
    cr
    @22
    @23
    ifcld
    #
    @23
    @5
    cQ
    cr
    cr
    opelxpi
    syl2anc
    elind
    ioombl1.g
    fmptd
    wph
    vn
    cn
    cP
    @5
    cop
    #
    @1
    cH
    @9
    cle
    @0
    @26
    @9
    cP
    @5
    cle
    wbr
    #
    @26
    cle
    wcel
    @9
    cP
    @3
    cle
    wbr
    #
    cP
    cQ
    cle
    wbr
    #
    @27
    @9
    cP
    cr
    wcel
    #
    @12
    @28
    @21
    @13
    cP
    cA
    max1
    syl2anc
    @9
    @15
    @17
    cP
    cQ
    cle
    @9
    @16
    @18
    @19
    @20
    simp3d
    ioombl1.p
    ioombl1.q
    3brtr4g
    @4
    @28
    @29
    @27
    @3
    cQ
    @3
    @5
    cP
    cle
    breq2
    cQ
    @5
    cP
    cle
    breq2
    ifboth
    syl2anc
    cP
    @5
    cle
    df-br
    sylib
    @9
    @30
    @24
    @26
    @0
    wcel
    @21
    @25
    cP
    @5
    cr
    cr
    opelxpi
    syl2anc
    elind
    ioombl1.h
    fmptd
    jca
end
