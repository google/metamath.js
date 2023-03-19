include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "clgs.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cif.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "cabs.mm"
include "cfv.mm"
include "cmul.mm"
include "cseq.mm"
include "lgsval.mm"
include "lgslem2.mm"
include "simp3i.mm"
include "simp2i.mm"
include "keepel.mm"
include "a1i.mm"
include "wn.mm"
include "simp1i.mm"
include "cn.mm"
include "cuz.mm"
include "wne.mm"
include "simplr.mm"
include "simpr.mm"
include "neqned.mm"
include "nnabscl.mm"
include "syl2anc.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "wf.mm"
include "cv.mm"
include "cfz.mm"
include "df-ne.mm"
include "lgsfcl2.mm"
include "3expa.mm"
include "sylan2br.mm"
include "elfznn.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "lgslem3.mm"
include "adantl.mm"
include "seqcl.mm"
include "sylancr.mm"
include "ifclda.mm"
include "eqeltrd.mm"

theorem lgscllem
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cN: class N
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  assume lgsval.1: |- F = ( n e. NN |-> if ( n e. Prime , ( if ( n = 2 , if ( 2 || A , 0 , if ( ( A mod 8 ) e. { 1 , 7 } , 1 , -u 1 ) ) , ( ( ( ( A ^ ( ( n - 1 ) / 2 ) ) + 1 ) mod n ) - 1 ) ) ^ ( n pCnt N ) ) , 1 ) )
  assume lgsfcl2.z: |- Z = { x e. ZZ | ( abs ` x ) <_ 1 }

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint F x
  disjoint N n
  disjoint N x
  disjoint Z n
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F a
  disjoint F m
  disjoint F y
  disjoint F z
  disjoint M n
  disjoint M x
  disjoint N a
  disjoint N m
  disjoint N y
  disjoint N z
  disjoint Z a
  disjoint Z b
  disjoint Z y
  disjoint Z z
  assert |- ( ( A e. ZZ /\ N e. ZZ ) -> ( A /L N ) e. Z )

  proof
    cA
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cA
    cN
    clgs
    co
    cN
    cc0
    wceq
    #
    cA
    c2
    cexp
    co
    c1
    wceq
    #
    c1
    cc0
    cif
    #
    cN
    cc0
    clt
    wbr
    cA
    cc0
    clt
    wbr
    wa
    #
    c1
    cneg
    #
    c1
    cif
    #
    cN
    cabs
    cfv
    #
    cmul
    cF
    c1
    cseq
    cfv
    #
    cmul
    co
    #
    cif
    cZ
    cA
    vn
    cF
    cN
    lgsval.1
    lgsval
    @2
    @3
    @5
    @11
    cZ
    @5
    cZ
    wcel
    @2
    @3
    wa
    @4
    c1
    cc0
    cZ
    @7
    cZ
    wcel
    #
    cc0
    cZ
    wcel
    #
    c1
    cZ
    wcel
    #
    vx
    cZ
    lgsfcl2.z
    lgslem2
    #
    simp3i
    #
    @12
    @13
    @14
    @15
    simp2i
    keepel
    a1i
    @2
    @3
    wn
    #
    wa
    #
    @8
    cZ
    wcel
    @10
    cZ
    wcel
    @11
    cZ
    wcel
    @6
    @7
    c1
    cZ
    @12
    @13
    @14
    @15
    simp1i
    @16
    keepel
    @18
    vy
    vz
    cmul
    cZ
    cF
    c1
    @9
    @18
    @9
    cn
    c1
    cuz
    cfv
    @18
    @1
    cN
    cc0
    wne
    #
    @9
    cn
    wcel
    @0
    @1
    @17
    simplr
    @18
    cN
    cc0
    @2
    @17
    simpr
    neqned
    cN
    nnabscl
    syl2anc
    nnuz
    syl6eleq
    @18
    cn
    cZ
    cF
    wf
    #
    vy
    cv
    #
    cn
    wcel
    @21
    cF
    cfv
    cZ
    wcel
    @21
    c1
    @9
    cfz
    co
    wcel
    @17
    @2
    @19
    @20
    cN
    cc0
    df-ne
    @0
    @1
    @19
    @20
    vx
    cA
    vn
    cF
    cN
    cZ
    lgsval.1
    lgsfcl2.z
    lgsfcl2
    3expa
    sylan2br
    @21
    @9
    elfznn
    cn
    cZ
    @21
    cF
    ffvelrn
    syl2an
    @21
    cZ
    wcel
    vz
    cv
    #
    cZ
    wcel
    wa
    @21
    @22
    cmul
    co
    cZ
    wcel
    @18
    vx
    @21
    @22
    cZ
    lgsfcl2.z
    lgslem3
    adantl
    seqcl
    vx
    @8
    @10
    cZ
    lgsfcl2.z
    lgslem3
    sylancr
    ifclda
    eqeltrd
end
