include "wcel.mm"
include "cuni.mm"
include "cphtpc.mm"
include "cfv.mm"
include "cqs.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cec.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wrex.mm"
include "cbs.mm"
include "a1i.mm"
include "pi1bas2.mm"
include "eleq2d.mm"
include "cvv.mm"
include "elex.mm"
include "id.mm"
include "fvex.mm"
include "ecexg.mm"
include "ax-mp.mm"
include "syl6eqel.mm"
include "rexlimivw.mm"
include "elqsg.mm"
include "pm5.21nii.mm"
include "w3a.mm"
include "pi1eluni.mm"
include "3anass.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "anass.mm"
include "rexbidv2.mm"
include "syl5bb.mm"
include "bitrd.mm"

theorem elpi1
  let wph: wff ph
  let cB: class B
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let c.pl: class .+
  let cM: class M
  let cN: class N
  assume elpi1.g: |- G = ( J pi1 Y )
  assume elpi1.b: |- B = ( Base ` G )
  assume elpi1.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume elpi1.2: |- ( ph -> Y e. X )

  disjoint F f
  disjoint G f
  disjoint X f
  disjoint B f
  disjoint J f
  disjoint f ph
  disjoint Y f
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint .+ a
  disjoint b c
  disjoint b d
  disjoint .+ b
  disjoint c d
  disjoint .+ c
  disjoint .+ d
  disjoint M c
  disjoint M d
  disjoint N c
  disjoint N d
  disjoint a f
  disjoint B a
  disjoint b f
  disjoint B b
  disjoint c f
  disjoint B c
  disjoint d f
  disjoint B d
  disjoint J a
  disjoint J b
  disjoint J c
  disjoint J d
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint Y c
  disjoint Y d
  assert |- ( ph -> ( F e. B <-> E. f e. ( II Cn J ) ( ( ( f ` 0 ) = Y /\ ( f ` 1 ) = Y ) /\ F = [ f ] ( ~=ph ` J ) ) ) )

  proof
    wph
    cF
    cB
    wcel
    cF
    cB
    cuni
    #
    cJ
    cphtpc
    cfv
    #
    cqs
    #
    wcel
    #
    cc0
    vf
    cv
    #
    cfv
    cY
    wceq
    #
    c1
    @4
    cfv
    cY
    wceq
    #
    wa
    #
    cF
    @4
    @1
    cec
    #
    wceq
    #
    wa
    #
    vf
    cii
    cJ
    ccn
    co
    #
    wrex
    #
    wph
    cB
    @2
    cF
    wph
    cB
    cG
    cJ
    cX
    cY
    elpi1.g
    elpi1.1
    elpi1.2
    cB
    cG
    cbs
    cfv
    wceq
    wph
    elpi1.b
    a1i
    #
    pi1bas2
    eleq2d
    @3
    @9
    vf
    @0
    wrex
    #
    wph
    @12
    @3
    cF
    cvv
    wcel
    #
    @14
    cF
    @2
    elex
    @9
    @15
    vf
    @0
    @9
    cF
    @8
    cvv
    @9
    id
    @1
    cvv
    wcel
    @8
    cvv
    wcel
    cJ
    cphtpc
    fvex
    @4
    cvv
    @1
    ecexg
    ax-mp
    syl6eqel
    rexlimivw
    vf
    @0
    cF
    @1
    cvv
    elqsg
    pm5.21nii
    wph
    @9
    @10
    vf
    @0
    @11
    wph
    @4
    @0
    wcel
    #
    @9
    wa
    @4
    @11
    wcel
    #
    @7
    wa
    #
    @9
    wa
    @17
    @10
    wa
    wph
    @16
    @18
    @9
    wph
    @16
    @17
    @5
    @6
    w3a
    @18
    wph
    cB
    @4
    cG
    cJ
    cX
    cY
    elpi1.g
    elpi1.1
    elpi1.2
    @13
    pi1eluni
    @17
    @5
    @6
    3anass
    syl6bb
    anbi1d
    @17
    @7
    @9
    anass
    syl6bb
    rexbidv2
    syl5bb
    bitrd
end
