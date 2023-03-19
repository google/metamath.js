include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "recnd.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "isumsup2.mm"
include "syl5eqbrr.mm"
include "isumclim.mm"

theorem isumsup
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  assume isumsup.1: |- Z = ( ZZ>= ` M )
  assume isumsup.2: |- G = seq M ( + , F )
  assume isumsup.3: |- ( ph -> M e. ZZ )
  assume isumsup.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume isumsup.5: |- ( ( ph /\ k e. Z ) -> A e. RR )
  assume isumsup.6: |- ( ( ph /\ k e. Z ) -> 0 <_ A )
  assume isumsup.7: |- ( ph -> E. x e. RR A. j e. Z ( G ` j ) <_ x )

  disjoint j x
  disjoint A j
  disjoint A x
  disjoint j k
  disjoint F j
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint M j
  disjoint M k
  disjoint M x
  disjoint j ph
  disjoint k ph
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint G j
  disjoint G x
  assert |- ( ph -> sum_ k e. Z A = sup ( ran G , RR , < ) )

  proof
    wph
    cA
    cG
    crn
    cr
    clt
    csup
    #
    vk
    cF
    cM
    cZ
    isumsup.1
    isumsup.3
    isumsup.4
    wph
    vk
    cv
    cZ
    wcel
    wa
    cA
    isumsup.5
    recnd
    wph
    caddc
    cF
    cM
    cseq
    cG
    @0
    cli
    isumsup.2
    wph
    vx
    cA
    vj
    vk
    cF
    cG
    cM
    cZ
    isumsup.1
    isumsup.2
    isumsup.3
    isumsup.4
    isumsup.5
    isumsup.6
    isumsup.7
    isumsup2
    syl5eqbrr
    isumclim
end
