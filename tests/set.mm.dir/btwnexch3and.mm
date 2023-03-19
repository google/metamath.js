include "wa.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wi.mm"
include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "btwnexch3.mm"
include "syl122anc.mm"
include "adantr.mm"
include "mp2and.mm"

theorem btwnexch3and
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  let vx: setvar x
  assume btwnexch3and.1: |- ( ph -> N e. NN )
  assume btwnexch3and.2: |- ( ph -> A e. ( EE ` N ) )
  assume btwnexch3and.3: |- ( ph -> B e. ( EE ` N ) )
  assume btwnexch3and.4: |- ( ph -> C e. ( EE ` N ) )
  assume btwnexch3and.5: |- ( ph -> D e. ( EE ` N ) )
  assume btwnexch3and.6: |- ( ( ph /\ ps ) -> B Btwn <. A , C >. )
  assume btwnexch3and.7: |- ( ( ph /\ ps ) -> C Btwn <. A , D >. )


  assert |- ( ( ph /\ ps ) -> C Btwn <. B , D >. )

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
    cbtwn
    wbr
    #
    cC
    cB
    cD
    cop
    cbtwn
    wbr
    #
    btwnexch3and.6
    btwnexch3and.7
    wph
    @0
    @1
    wa
    @2
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
    @4
    wcel
    cC
    @4
    wcel
    cD
    @4
    wcel
    @3
    btwnexch3and.1
    btwnexch3and.2
    btwnexch3and.3
    btwnexch3and.4
    btwnexch3and.5
    cA
    cB
    cC
    cD
    cN
    btwnexch3
    syl122anc
    adantr
    mp2and
end
