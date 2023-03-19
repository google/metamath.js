include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "caddc.mm"
include "cv.mm"
include "cfv.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "cr.mm"
include "crab.mm"
include "clt.mm"
include "csup.mm"
include "wss.mm"
include "ssrab2.mm"
include "ressxr.mm"
include "sstri.mm"
include "supxrcl.mm"
include "mp1i.mm"
include "syl5eqel.mm"
include "radcnv0.mm"
include "supxrub.mm"
include "sylancr.mm"
include "syl6breqr.mm"
include "pnfge.mm"
include "syl.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "pnfxr.mm"
include "elicc1.mm"
include "mp2an.mm"
include "syl3anbrc.mm"

theorem radcnvcl
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cR: class R
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
  let cY: class Y
  assume pser.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )
  assume radcnv.a: |- ( ph -> A : NN0 --> CC )
  assume radcnv.r: |- R = sup ( { r e. RR | seq 0 ( + , ( G ` r ) ) e. dom ~~> } , RR* , < )

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
  assert |- ( ph -> R e. ( 0 [,] +oo ) )

  proof
    wph
    cR
    cxr
    wcel
    #
    cc0
    cR
    cle
    wbr
    #
    cR
    cpnf
    cle
    wbr
    #
    cR
    cc0
    cpnf
    cicc
    co
    wcel
    #
    wph
    cR
    caddc
    vr
    cv
    cG
    cfv
    cc0
    cseq
    cli
    cdm
    wcel
    #
    vr
    cr
    crab
    #
    cxr
    clt
    csup
    #
    cxr
    radcnv.r
    @5
    cxr
    wss
    #
    @6
    cxr
    wcel
    wph
    @5
    cr
    cxr
    @4
    vr
    cr
    ssrab2
    ressxr
    sstri
    #
    @5
    supxrcl
    mp1i
    syl5eqel
    #
    wph
    cc0
    @6
    cR
    cle
    wph
    @7
    cc0
    @5
    wcel
    cc0
    @6
    cle
    wbr
    @8
    wph
    vx
    cA
    vn
    cG
    vr
    pser.g
    radcnv.a
    radcnv0
    @5
    cc0
    supxrub
    sylancr
    radcnv.r
    syl6breqr
    wph
    @0
    @2
    @9
    cR
    pnfge
    syl
    cc0
    cxr
    wcel
    cpnf
    cxr
    wcel
    @3
    @0
    @1
    @2
    w3a
    wb
    0xr
    pnfxr
    cc0
    cpnf
    cR
    elicc1
    mp2an
    syl3anbrc
end
