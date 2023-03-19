include "cc0.mm"
include "cr.mm"
include "wcel.mm"
include "caddc.mm"
include "cfv.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "cv.mm"
include "crab.mm"
include "0red.mm"
include "csn.mm"
include "cn0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "cfn.mm"
include "snfi.mm"
include "a1i.mm"
include "0nn0.mm"
include "snssd.mm"
include "wa.mm"
include "cif.mm"
include "ifid.mm"
include "wn.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "cc.mm"
include "0cnd.mm"
include "pserval2.mm"
include "sylan.mm"
include "adantr.mm"
include "cn.mm"
include "wo.mm"
include "simpr.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "velsn.mm"
include "syl6ibr.mm"
include "con1d.mm"
include "imp.mm"
include "0expd.mm"
include "oveq2d.mm"
include "ffvelrnda.mm"
include "mul01d.mm"
include "3eqtrd.mm"
include "ifeq2da.mm"
include "syl5eqr.mm"
include "sselda.mm"
include "psergf.mm"
include "syldan.mm"
include "fsumcvg3.mm"
include "fveq2.mm"
include "seqeq3d.mm"
include "eleq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"

theorem radcnv0
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let cG: class G
  let vr: setvar r
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vs: setvar s
  let vy: setvar y
  let vj: setvar j
  let cH: class H
  let cX: class X
  let cN: class N
  let cR: class R
  let cY: class Y
  assume pser.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )
  assume radcnv.a: |- ( ph -> A : NN0 --> CC )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint G r
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i s
  disjoint i x
  disjoint i y
  disjoint A i
  disjoint k m
  disjoint k n
  disjoint k s
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n s
  disjoint n y
  disjoint s x
  disjoint s y
  disjoint A s
  disjoint x y
  disjoint A y
  disjoint j m
  disjoint j s
  disjoint H j
  disjoint H m
  disjoint H s
  disjoint i j
  disjoint i ph
  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph s
  disjoint X i
  disjoint X k
  disjoint X m
  disjoint X s
  disjoint X y
  disjoint j r
  disjoint j y
  disjoint G j
  disjoint k r
  disjoint G k
  disjoint m r
  disjoint G m
  disjoint r s
  disjoint r y
  disjoint G s
  disjoint G y
  disjoint N n
  disjoint N y
  disjoint R k
  disjoint R y
  disjoint Y i
  disjoint Y j
  disjoint Y k
  disjoint Y m
  assert |- ( ph -> 0 e. { r e. RR | seq 0 ( + , ( G ` r ) ) e. dom ~~> } )

  proof
    wph
    cc0
    cr
    wcel
    caddc
    cc0
    cG
    cfv
    #
    cc0
    cseq
    #
    cli
    cdm
    #
    wcel
    #
    cc0
    caddc
    vr
    cv
    #
    cG
    cfv
    #
    cc0
    cseq
    #
    @2
    wcel
    #
    vr
    cr
    crab
    wcel
    wph
    0red
    wph
    cc0
    csn
    #
    vk
    cv
    #
    @0
    cfv
    #
    vk
    @0
    cc0
    cn0
    nn0uz
    wph
    0zd
    @8
    cfn
    wcel
    wph
    cc0
    snfi
    a1i
    wph
    cc0
    cn0
    cc0
    cn0
    wcel
    wph
    0nn0
    a1i
    snssd
    #
    wph
    @9
    cn0
    wcel
    #
    wa
    #
    @10
    @9
    @8
    wcel
    #
    @10
    @10
    cif
    @14
    @10
    cc0
    cif
    @14
    @10
    ifid
    @13
    @14
    @10
    cc0
    @10
    @13
    @14
    wn
    #
    wa
    #
    @10
    @9
    cA
    cfv
    #
    cc0
    @9
    cexp
    co
    #
    cmul
    co
    #
    @17
    cc0
    cmul
    co
    cc0
    @13
    @10
    @19
    wceq
    #
    @15
    wph
    cc0
    cc
    wcel
    @12
    @20
    wph
    0cnd
    #
    vx
    cA
    vn
    cG
    @9
    cc0
    pser.g
    pserval2
    sylan
    adantr
    @16
    @18
    cc0
    @17
    cmul
    @16
    @9
    @13
    @15
    @9
    cn
    wcel
    #
    @13
    @22
    @14
    @13
    @22
    wn
    @9
    cc0
    wceq
    #
    @14
    @13
    @22
    @23
    @13
    @12
    @22
    @23
    wo
    wph
    @12
    simpr
    @9
    elnn0
    sylib
    ord
    vk
    cc0
    velsn
    syl6ibr
    con1d
    imp
    0expd
    oveq2d
    @16
    @17
    @13
    @17
    cc
    wcel
    @15
    wph
    cn0
    cc
    @9
    cA
    radcnv.a
    ffvelrnda
    adantr
    mul01d
    3eqtrd
    ifeq2da
    syl5eqr
    wph
    @14
    @12
    @10
    cc
    wcel
    wph
    @8
    cn0
    @9
    @11
    sselda
    wph
    cn0
    cc
    @9
    @0
    wph
    vx
    cA
    vn
    cG
    cc0
    pser.g
    radcnv.a
    @21
    psergf
    ffvelrnda
    syldan
    fsumcvg3
    @7
    @3
    vr
    cc0
    cr
    @4
    cc0
    wceq
    #
    @6
    @1
    @2
    @24
    @5
    @0
    caddc
    cc0
    @4
    cc0
    cG
    fveq2
    seqeq3d
    eleq1d
    elrab
    sylanbrc
end
