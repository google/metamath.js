include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "meaiuninc.mm"

theorem meaiuninc2
  let wph: wff ph
  let cB: class B
  let cS: class S
  let vn: setvar n
  let cE: class E
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vx: setvar x
  let vk: setvar k
  assume meaiuninc2.m: |- ( ph -> M e. Meas )
  assume meaiuninc2.n: |- ( ph -> N e. ZZ )
  assume meaiuninc2.z: |- Z = ( ZZ>= ` N )
  assume meaiuninc2.e: |- ( ph -> E : Z --> dom M )
  assume meaiuninc2.i: |- ( ( ph /\ n e. Z ) -> ( E ` n ) C_ ( E ` ( n + 1 ) ) )
  assume meaiuninc2.b: |- ( ph -> B e. RR )
  assume meaiuninc2.x: |- ( ( ph /\ n e. Z ) -> ( M ` ( E ` n ) ) <_ B )
  assume meaiuninc2.s: |- S = ( n e. Z |-> ( M ` ( E ` n ) ) )

  disjoint B n
  disjoint E n
  disjoint M n
  disjoint N n
  disjoint Z n
  disjoint n ph
  disjoint B x
  disjoint n x
  disjoint E x
  disjoint M x
  disjoint N x
  disjoint Z x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> S ~~> ( M ` U_ n e. Z ( E ` n ) ) )

  proof
    wph
    vx
    cS
    vn
    cE
    cM
    cN
    cZ
    meaiuninc2.m
    meaiuninc2.n
    meaiuninc2.z
    meaiuninc2.e
    meaiuninc2.i
    wph
    cB
    cr
    wcel
    vn
    cv
    cE
    cfv
    cM
    cfv
    #
    cB
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    @0
    vx
    cv
    #
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    vx
    cr
    wrex
    meaiuninc2.b
    wph
    @1
    vn
    cZ
    meaiuninc2.x
    ralrimiva
    @5
    @2
    vx
    cB
    cr
    @3
    cB
    wceq
    @4
    @1
    vn
    cZ
    @3
    cB
    @0
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    meaiuninc2.s
    meaiuninc
end
