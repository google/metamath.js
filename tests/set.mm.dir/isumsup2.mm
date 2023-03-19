include "cr.mm"
include "caddc.mm"
include "cseq.mm"
include "wf.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "eqeltrd.mm"
include "serfre.mm"
include "feq1i.mm"
include "sylibr.mm"
include "c1.mm"
include "co.mm"
include "cle.mm"
include "cuz.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "cz.mm"
include "eluzelz.mm"
include "uzid.mm"
include "peano2uz.mm"
include "4syl.mm"
include "cfz.mm"
include "simpl.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "syl2an.mm"
include "cc0.mm"
include "wbr.mm"
include "peano2uzs.mm"
include "adantl.mm"
include "uztrn2.mm"
include "breqtrrd.mm"
include "adantlr.mm"
include "syldan.mm"
include "sermono.mm"
include "fveq1i.mm"
include "3brtr4g.mm"
include "climsup.mm"

theorem isumsup2
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
  assert |- ( ph -> G ~~> sup ( ran G , RR , < ) )

  proof
    wph
    vx
    vj
    cG
    cM
    cZ
    isumsup.1
    isumsup.3
    wph
    cZ
    cr
    caddc
    cF
    cM
    cseq
    #
    wf
    cZ
    cr
    cG
    wf
    wph
    vk
    cF
    cM
    cZ
    isumsup.1
    isumsup.3
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @1
    cF
    cfv
    #
    cA
    cr
    isumsup.4
    isumsup.5
    eqeltrd
    #
    serfre
    cZ
    cr
    cG
    @0
    isumsup.2
    feq1i
    sylibr
    wph
    vj
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @6
    @0
    cfv
    @6
    c1
    caddc
    co
    #
    @0
    cfv
    @6
    cG
    cfv
    @9
    cG
    cfv
    cle
    @8
    vk
    cF
    @6
    cM
    @9
    @8
    @6
    cZ
    cM
    cuz
    cfv
    #
    wph
    @7
    simpr
    isumsup.1
    syl6eleq
    #
    @8
    @6
    @10
    wcel
    @6
    cz
    wcel
    @6
    @6
    cuz
    cfv
    #
    wcel
    @9
    @12
    wcel
    @11
    cM
    @6
    eluzelz
    @6
    uzid
    @6
    @6
    peano2uz
    4syl
    @8
    wph
    @2
    @4
    cr
    wcel
    @1
    cM
    @9
    cfz
    co
    wcel
    #
    wph
    @7
    simpl
    @13
    @1
    @10
    cZ
    @1
    cM
    @9
    elfzuz
    isumsup.1
    syl6eleqr
    @5
    syl2an
    @8
    @1
    @9
    @9
    cfz
    co
    wcel
    #
    @2
    cc0
    @4
    cle
    wbr
    #
    @8
    @9
    cZ
    wcel
    #
    @1
    @9
    cuz
    cfv
    wcel
    @2
    @14
    @7
    @16
    wph
    cM
    @6
    cZ
    isumsup.1
    peano2uzs
    adantl
    @1
    @9
    @9
    elfzuz
    cM
    @1
    @9
    cZ
    isumsup.1
    uztrn2
    syl2an
    wph
    @2
    @15
    @7
    @3
    cc0
    cA
    @4
    cle
    isumsup.6
    isumsup.4
    breqtrrd
    adantlr
    syldan
    sermono
    @6
    cG
    @0
    isumsup.2
    fveq1i
    @9
    cG
    @0
    isumsup.2
    fveq1i
    3brtr4g
    isumsup.7
    climsup
end
