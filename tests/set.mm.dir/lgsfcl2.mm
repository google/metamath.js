include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cn.mm"
include "cv.mm"
include "cprime.mm"
include "c2.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "c8.mm"
include "cmo.mm"
include "co.mm"
include "c1.mm"
include "c7.mm"
include "cpr.mm"
include "cneg.mm"
include "cif.mm"
include "cmin.mm"
include "cdiv.mm"
include "cexp.mm"
include "caddc.mm"
include "cpc.mm"
include "wa.mm"
include "cn0.mm"
include "cle.mm"
include "0z.mm"
include "0le1.mm"
include "cabs.mm"
include "cfv.mm"
include "fveq2.mm"
include "abs0.mm"
include "syl6eq.mm"
include "breq1d.mm"
include "elrab2.mm"
include "mpbir2an.mm"
include "1z.mm"
include "1le1.mm"
include "abs1.mm"
include "neg1z.mm"
include "ax-1cn.mm"
include "absnegi.mm"
include "eqtri.mm"
include "keepel.mm"
include "a1i.mm"
include "wn.mm"
include "csn.mm"
include "cdif.mm"
include "simpl1.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "neqned.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "lgslem4.mm"
include "syl2anc.mm"
include "ifclda.mm"
include "simpll2.mm"
include "simpll3.mm"
include "pczcl.mm"
include "syl12anc.mm"
include "cc.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "zsscn.mm"
include "sstri.mm"
include "lgslem3.mm"
include "expcllem.mm"
include "fmptd.mm"

theorem lgsfcl2
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
  assert |- ( ( A e. ZZ /\ N e. ZZ /\ N =/= 0 ) -> F : NN --> Z )

  proof
    cA
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cN
    cc0
    wne
    #
    w3a
    #
    vn
    cn
    vn
    cv
    #
    cprime
    wcel
    #
    @4
    c2
    wceq
    #
    c2
    cA
    cdvds
    wbr
    #
    cc0
    cA
    c8
    cmo
    co
    c1
    c7
    cpr
    wcel
    #
    c1
    c1
    cneg
    #
    cif
    #
    cif
    #
    cA
    @4
    c1
    cmin
    co
    c2
    cdiv
    co
    cexp
    co
    c1
    caddc
    co
    @4
    cmo
    co
    c1
    cmin
    co
    #
    cif
    #
    @4
    cN
    cpc
    co
    #
    cexp
    co
    #
    c1
    cif
    cZ
    cF
    @3
    @4
    cn
    wcel
    #
    wa
    #
    @5
    @15
    c1
    cZ
    @17
    @5
    wa
    #
    @13
    cZ
    wcel
    @14
    cn0
    wcel
    #
    @15
    cZ
    wcel
    @18
    @6
    @11
    @12
    cZ
    @11
    cZ
    wcel
    @18
    @6
    wa
    @7
    cc0
    @10
    cZ
    cc0
    cZ
    wcel
    cc0
    cz
    wcel
    cc0
    c1
    cle
    wbr
    #
    0z
    0le1
    vx
    cv
    #
    cabs
    cfv
    #
    c1
    cle
    wbr
    #
    @20
    vx
    cc0
    cz
    cZ
    @21
    cc0
    wceq
    #
    @22
    cc0
    c1
    cle
    @24
    @22
    cc0
    cabs
    cfv
    cc0
    @21
    cc0
    cabs
    fveq2
    abs0
    syl6eq
    breq1d
    lgsfcl2.z
    elrab2
    mpbir2an
    @8
    c1
    @9
    cZ
    c1
    cZ
    wcel
    #
    c1
    cz
    wcel
    c1
    c1
    cle
    wbr
    #
    1z
    1le1
    @23
    @26
    vx
    c1
    cz
    cZ
    @21
    c1
    wceq
    #
    @22
    c1
    c1
    cle
    @27
    @22
    c1
    cabs
    cfv
    #
    c1
    @21
    c1
    cabs
    fveq2
    abs1
    syl6eq
    breq1d
    lgsfcl2.z
    elrab2
    mpbir2an
    #
    @9
    cZ
    wcel
    @9
    cz
    wcel
    @26
    neg1z
    1le1
    @23
    @26
    vx
    @9
    cz
    cZ
    @21
    @9
    wceq
    #
    @22
    c1
    c1
    cle
    @30
    @22
    @9
    cabs
    cfv
    #
    c1
    @21
    @9
    cabs
    fveq2
    @31
    @28
    c1
    c1
    ax-1cn
    absnegi
    abs1
    eqtri
    syl6eq
    breq1d
    lgsfcl2.z
    elrab2
    mpbir2an
    keepel
    keepel
    a1i
    @18
    @6
    wn
    #
    wa
    #
    @0
    @4
    cprime
    c2
    csn
    cdif
    wcel
    #
    @12
    cZ
    wcel
    @17
    @0
    @5
    @32
    @0
    @1
    @2
    @16
    simpl1
    ad2antrr
    @33
    @5
    @4
    c2
    wne
    @34
    @17
    @5
    @32
    simplr
    @33
    @4
    c2
    @18
    @32
    simpr
    neqned
    @4
    cprime
    c2
    eldifsn
    sylanbrc
    vx
    cA
    @4
    cZ
    lgsfcl2.z
    lgslem4
    syl2anc
    ifclda
    @18
    @5
    @1
    @2
    @19
    @17
    @5
    simpr
    @0
    @1
    @2
    @16
    @5
    simpll2
    @0
    @1
    @2
    @16
    @5
    simpll3
    @4
    cN
    pczcl
    syl12anc
    va
    vb
    @13
    @14
    cZ
    cZ
    cz
    cc
    cZ
    @23
    vx
    cz
    crab
    cz
    lgsfcl2.z
    @23
    vx
    cz
    ssrab2
    eqsstri
    zsscn
    sstri
    vx
    va
    cv
    vb
    cv
    cZ
    lgsfcl2.z
    lgslem3
    @29
    expcllem
    syl2anc
    @25
    @17
    @5
    wn
    wa
    @29
    a1i
    ifclda
    lgsval.1
    fmptd
end
