include "wa.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wb.mm"
include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "btwncom.mm"
include "syl13anc.mm"
include "adantr.mm"
include "mpbid.mm"

theorem btwncomand
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N
  assume btwncomand.1: |- ( ph -> N e. NN )
  assume btwncomand.2: |- ( ph -> A e. ( EE ` N ) )
  assume btwncomand.3: |- ( ph -> B e. ( EE ` N ) )
  assume btwncomand.4: |- ( ph -> C e. ( EE ` N ) )
  assume btwncomand.5: |- ( ( ph /\ ps ) -> A Btwn <. B , C >. )


  assert |- ( ( ph /\ ps ) -> A Btwn <. C , B >. )

  proof
    wph
    wps
    wa
    cA
    cB
    cC
    cop
    cbtwn
    wbr
    #
    cA
    cC
    cB
    cop
    cbtwn
    wbr
    #
    btwncomand.5
    wph
    @0
    @1
    wb
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
    @3
    wcel
    cC
    @3
    wcel
    @2
    btwncomand.1
    btwncomand.2
    btwncomand.3
    btwncomand.4
    cA
    cB
    cC
    cN
    btwncom
    syl13anc
    adantr
    mpbid
end
