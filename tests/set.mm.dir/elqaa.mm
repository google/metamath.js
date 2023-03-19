include "caa.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cq.mm"
include "cply.mm"
include "c0p.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "wa.mm"
include "cz.mm"
include "elaa.mm"
include "wss.mm"
include "wi.mm"
include "zssq.mm"
include "qsscn.mm"
include "plyss.mm"
include "mp2an.mm"
include "ssdif.mm"
include "ssrexv.mm"
include "mp2b.mm"
include "anim2i.mm"
include "sylbi.mm"
include "ccoe.mm"
include "cdgr.mm"
include "cmul.mm"
include "cn0.mm"
include "co.mm"
include "cn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cmpt.mm"
include "cseq.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "eqid.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "rabbidv.mm"
include "oveq2.mm"
include "cbvrabv.mm"
include "syl6eq.mm"
include "infeq1d.mm"
include "cbvmptv.mm"
include "elqaalem3.mm"
include "r19.29an.mm"
include "impbii.mm"

theorem elqaa
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let cP: class P
  let wph: wff ph
  let cF: class F
  let cK: class K
  let cN: class N
  let cR: class R

  disjoint A f
  disjoint f g
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B f
  disjoint B k
  disjoint B m
  disjoint B n
  disjoint B z
  disjoint i j
  disjoint P i
  disjoint P j
  disjoint i k
  disjoint i m
  disjoint i z
  disjoint i ph
  disjoint j k
  disjoint j m
  disjoint j z
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph z
  disjoint f i
  disjoint f j
  disjoint F f
  disjoint F i
  disjoint F j
  disjoint F m
  disjoint F z
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint K i
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint K j
  disjoint K k
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint R f
  disjoint R k
  disjoint R m
  disjoint R z
  assert |- ( A e. AA <-> ( A e. CC /\ E. f e. ( ( Poly ` QQ ) \ { 0p } ) ( f ` A ) = 0 ) )

  proof
    cA
    caa
    wcel
    #
    cA
    cc
    wcel
    #
    cA
    vf
    cv
    #
    cfv
    cc0
    wceq
    #
    vf
    cq
    cply
    cfv
    #
    c0p
    csn
    #
    cdif
    #
    wrex
    #
    wa
    #
    @0
    @1
    @3
    vf
    cz
    cply
    cfv
    #
    @5
    cdif
    #
    wrex
    #
    wa
    @8
    cA
    vf
    elaa
    @11
    @7
    @1
    @9
    @4
    wss
    #
    @10
    @6
    wss
    @11
    @7
    wi
    cz
    cq
    wss
    cq
    cc
    wss
    @12
    zssq
    qsscn
    cz
    cq
    plyss
    mp2an
    @9
    @4
    @5
    ssdif
    @3
    vf
    @10
    @6
    ssrexv
    mp2b
    anim2i
    sylbi
    @1
    @3
    @0
    vf
    @6
    @1
    @2
    @6
    wcel
    #
    wa
    #
    @3
    wa
    cA
    @2
    ccoe
    cfv
    #
    @2
    cdgr
    cfv
    cmul
    vm
    cn0
    vm
    cv
    #
    @15
    cfv
    #
    vj
    cv
    #
    cmul
    co
    #
    cz
    wcel
    #
    vj
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cmpt
    #
    cc0
    cseq
    cfv
    #
    vk
    vn
    @2
    @23
    @1
    @13
    @3
    simpll
    @1
    @13
    @3
    simplr
    @14
    @3
    simpr
    @15
    eqid
    vm
    vk
    cn0
    @22
    vk
    cv
    #
    @15
    cfv
    #
    vn
    cv
    #
    cmul
    co
    #
    cz
    wcel
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    @16
    @25
    wceq
    #
    cr
    @21
    @30
    clt
    @31
    @21
    @26
    @18
    cmul
    co
    #
    cz
    wcel
    #
    vj
    cn
    crab
    @30
    @31
    @20
    @33
    vj
    cn
    @31
    @19
    @32
    cz
    @31
    @17
    @26
    @18
    cmul
    @16
    @25
    @15
    fveq2
    oveq1d
    eleq1d
    rabbidv
    @33
    @29
    vj
    vn
    cn
    @18
    @27
    wceq
    @32
    @28
    cz
    @18
    @27
    @26
    cmul
    oveq2
    eleq1d
    cbvrabv
    syl6eq
    infeq1d
    cbvmptv
    @24
    eqid
    elqaalem3
    r19.29an
    impbii
end
