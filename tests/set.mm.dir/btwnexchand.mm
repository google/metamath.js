include "wa.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wi.mm"
include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "btwnexch.mm"
include "syl122anc.mm"
include "adantr.mm"
include "mp2and.mm"

theorem btwnexchand
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  assume btwnexchand.1: |- ( ph -> N e. NN )
  assume btwnexchand.2: |- ( ph -> A e. ( EE ` N ) )
  assume btwnexchand.3: |- ( ph -> B e. ( EE ` N ) )
  assume btwnexchand.4: |- ( ph -> C e. ( EE ` N ) )
  assume btwnexchand.5: |- ( ph -> D e. ( EE ` N ) )
  assume btwnexchand.6: |- ( ( ph /\ ps ) -> B Btwn <. A , C >. )
  assume btwnexchand.7: |- ( ( ph /\ ps ) -> C Btwn <. A , D >. )


  assert |- ( ( ph /\ ps ) -> B Btwn <. A , D >. )

  proof
    wph
    wps
    wa
    cB
    cA
    cC
    cop
    cbtwn
    wbr
    #
    cC
    cA
    cD
    cop
    #
    cbtwn
    wbr
    #
    cB
    @1
    cbtwn
    wbr
    #
    btwnexchand.6
    btwnexchand.7
    wph
    @0
    @2
    wa
    @3
    wi
    #
    wps
    wph
    cN
    cn
    wcel
    cA
    cN
    cee
    cfv
    #
    wcel
    cB
    @5
    wcel
    cC
    @5
    wcel
    cD
    @5
    wcel
    @4
    btwnexchand.1
    btwnexchand.2
    btwnexchand.3
    btwnexchand.4
    btwnexchand.5
    cA
    cB
    cC
    cD
    cN
    btwnexch
    syl122anc
    adantr
    mp2and
end
