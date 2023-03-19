include "cv.mm"
include "cr.mm"
include "cdv.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cicc.mm"
include "wrex.mm"
include "crn.mm"
include "wcel.mm"
include "dvivthlem1.mm"
include "wa.mm"
include "cioo.mm"
include "wfn.mm"
include "cc.mm"
include "wf.mm"
include "cdm.mm"
include "dvf.mm"
include "feq2d.mm"
include "mpbii.mm"
include "ffn.mm"
include "syl.mm"
include "adantr.mm"
include "wss.mm"
include "iccssioo2.mm"
include "syl2anc.mm"
include "sselda.mm"
include "fnfvelrn.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem dvivthlem2
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  assume dvivth.1: |- ( ph -> M e. ( A (,) B ) )
  assume dvivth.2: |- ( ph -> N e. ( A (,) B ) )
  assume dvivth.3: |- ( ph -> F e. ( ( A (,) B ) -cn-> RR ) )
  assume dvivth.4: |- ( ph -> dom ( RR _D F ) = ( A (,) B ) )
  assume dvivth.5: |- ( ph -> M < N )
  assume dvivth.6: |- ( ph -> C e. ( ( ( RR _D F ) ` N ) [,] ( ( RR _D F ) ` M ) ) )
  assume dvivth.7: |- G = ( y e. ( A (,) B ) |-> ( ( F ` y ) - ( C x. y ) ) )

  disjoint A y
  disjoint B y
  disjoint F y
  disjoint M y
  disjoint C y
  disjoint N y
  disjoint ph y
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x y
  disjoint A x
  disjoint B w
  disjoint B x
  disjoint F w
  disjoint F x
  disjoint w z
  disjoint G w
  disjoint x z
  disjoint G x
  disjoint G z
  disjoint M w
  disjoint M x
  disjoint y z
  disjoint M z
  disjoint C x
  disjoint N w
  disjoint N x
  disjoint N z
  disjoint ph w
  disjoint ph x
  disjoint ph z
  assert |- ( ph -> C e. ran ( RR _D F ) )

  proof
    wph
    vx
    cv
    #
    cr
    cF
    cdv
    co
    #
    cfv
    #
    cC
    wceq
    #
    vx
    cM
    cN
    cicc
    co
    #
    wrex
    cC
    @1
    crn
    #
    wcel
    #
    wph
    vx
    vy
    cA
    cB
    cC
    cF
    cG
    cM
    cN
    dvivth.1
    dvivth.2
    dvivth.3
    dvivth.4
    dvivth.5
    dvivth.6
    dvivth.7
    dvivthlem1
    wph
    @3
    @6
    vx
    @4
    wph
    @0
    @4
    wcel
    #
    wa
    #
    @2
    @5
    wcel
    #
    @3
    @6
    @8
    @1
    cA
    cB
    cioo
    co
    #
    wfn
    #
    @0
    @10
    wcel
    @9
    wph
    @11
    @7
    wph
    @10
    cc
    @1
    wf
    #
    @11
    wph
    @1
    cdm
    #
    cc
    @1
    wf
    @12
    cF
    dvf
    wph
    @13
    @10
    cc
    @1
    dvivth.4
    feq2d
    mpbii
    @10
    cc
    @1
    ffn
    syl
    adantr
    wph
    @4
    @10
    @0
    wph
    cM
    @10
    wcel
    cN
    @10
    wcel
    @4
    @10
    wss
    dvivth.1
    dvivth.2
    cA
    cB
    cM
    cN
    iccssioo2
    syl2anc
    sselda
    @10
    @0
    @1
    fnfvelrn
    syl2anc
    @2
    cC
    @5
    eleq1
    syl5ibcom
    rexlimdva
    mpd
end
