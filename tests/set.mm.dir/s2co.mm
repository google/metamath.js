include "cs1.mm"
include "cs2.mm"
include "cfv.mm"
include "df-s2.mm"
include "s1cld.mm"
include "wcel.mm"
include "wf.mm"
include "ccom.mm"
include "wceq.mm"
include "s1co.mm"
include "syl2anc.mm"
include "cats1co.mm"

theorem s2co
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let cY: class Y
  assume s2co.1: |- ( ph -> F : X --> Y )
  assume s2co.2: |- ( ph -> A e. X )
  assume s2co.3: |- ( ph -> B e. X )


  assert |- ( ph -> ( F o. <" A B "> ) = <" ( F ` A ) ( F ` B ) "> )

  proof
    wph
    cX
    cY
    cA
    cs1
    #
    cA
    cB
    cs2
    cA
    cF
    cfv
    #
    cs1
    #
    cF
    @1
    cB
    cF
    cfv
    #
    cs2
    cB
    cA
    cB
    df-s2
    wph
    cA
    cX
    s2co.2
    s1cld
    s2co.3
    s2co.1
    wph
    cA
    cX
    wcel
    cX
    cY
    cF
    wf
    cF
    @0
    ccom
    @2
    wceq
    s2co.2
    s2co.1
    cX
    cY
    cA
    cF
    s1co
    syl2anc
    @1
    @3
    df-s2
    cats1co
end
