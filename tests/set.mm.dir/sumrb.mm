include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wb.mm"
include "wa.mm"
include "cres.mm"
include "cz.mm"
include "cvv.mm"
include "adantr.mm"
include "seqex.mm"
include "climres.mm"
include "sylancl.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "cc.mm"
include "adantlr.mm"
include "simpr.mm"
include "sumrblem.mm"
include "mpidan.mm"
include "breq1d.mm"
include "bitr3d.mm"
include "wo.mm"
include "uztric.mm"
include "syl2anc.mm"
include "mpjaodan.mm"

theorem sumrb
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cH: class H
  let cK: class K
  assume summo.1: |- F = ( k e. ZZ |-> if ( k e. A , B , 0 ) )
  assume summo.2: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume sumrb.4: |- ( ph -> M e. ZZ )
  assume sumrb.5: |- ( ph -> N e. ZZ )
  assume sumrb.6: |- ( ph -> A C_ ( ZZ>= ` M ) )
  assume sumrb.7: |- ( ph -> A C_ ( ZZ>= ` N ) )

  disjoint A k
  disjoint F k
  disjoint N k
  disjoint k ph
  disjoint M k
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint A i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F f
  disjoint F g
  disjoint F j
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint G g
  disjoint G i
  disjoint G j
  disjoint G k
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint H i
  disjoint H x
  disjoint K i
  disjoint K j
  disjoint K k
  disjoint K m
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint N m
  disjoint N n
  disjoint g ph
  disjoint i ph
  disjoint j ph
  disjoint m ph
  disjoint n ph
  disjoint ph y
  disjoint B f
  disjoint B j
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint M i
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint M y
  assert |- ( ph -> ( seq M ( + , F ) ~~> C <-> seq N ( + , F ) ~~> C ) )

  proof
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    caddc
    cF
    cM
    cseq
    #
    cC
    cli
    wbr
    #
    caddc
    cF
    cN
    cseq
    #
    cC
    cli
    wbr
    #
    wb
    cM
    cN
    cuz
    cfv
    #
    wcel
    #
    wph
    @1
    wa
    #
    @2
    @6
    cres
    #
    cC
    cli
    wbr
    #
    @3
    @5
    @8
    cN
    cz
    wcel
    #
    @2
    cvv
    wcel
    @10
    @3
    wb
    wph
    @11
    @1
    sumrb.5
    adantr
    caddc
    cF
    cM
    seqex
    cC
    @2
    cN
    cvv
    climres
    sylancl
    @8
    @9
    @4
    cC
    cli
    wph
    @1
    cA
    @6
    wss
    @9
    @4
    wceq
    sumrb.7
    @8
    cA
    cB
    vk
    cF
    cM
    cN
    summo.1
    wph
    vk
    cv
    cA
    wcel
    #
    cB
    cc
    wcel
    #
    @1
    summo.2
    adantlr
    wph
    @1
    simpr
    sumrblem
    mpidan
    breq1d
    bitr3d
    wph
    @7
    wa
    #
    @4
    @0
    cres
    #
    cC
    cli
    wbr
    #
    @3
    @5
    @14
    @15
    @2
    cC
    cli
    wph
    @7
    cA
    @0
    wss
    @15
    @2
    wceq
    sumrb.6
    @14
    cA
    cB
    vk
    cF
    cN
    cM
    summo.1
    wph
    @12
    @13
    @7
    summo.2
    adantlr
    wph
    @7
    simpr
    sumrblem
    mpidan
    breq1d
    @14
    cM
    cz
    wcel
    #
    @4
    cvv
    wcel
    @16
    @5
    wb
    wph
    @17
    @7
    sumrb.4
    adantr
    caddc
    cF
    cN
    seqex
    cC
    @4
    cM
    cvv
    climres
    sylancl
    bitr3d
    wph
    @17
    @11
    @1
    @7
    wo
    sumrb.4
    sumrb.5
    cM
    cN
    uztric
    syl2anc
    mpjaodan
end
