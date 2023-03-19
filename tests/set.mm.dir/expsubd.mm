include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cdiv.mm"
include "wceq.mm"
include "expsub.mm"
include "syl22anc.mm"

theorem expsubd
  let wph: wff ph
  let cA: class A
  let cM: class M
  let cN: class N
  assume expcld.1: |- ( ph -> A e. CC )
  assume sqrecd.1: |- ( ph -> A =/= 0 )
  assume expclzd.3: |- ( ph -> N e. ZZ )
  assume expsubd.3: |- ( ph -> M e. ZZ )


  assert |- ( ph -> ( A ^ ( M - N ) ) = ( ( A ^ M ) / ( A ^ N ) ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    wne
    cM
    cz
    wcel
    cN
    cz
    wcel
    cA
    cM
    cN
    cmin
    co
    cexp
    co
    cA
    cM
    cexp
    co
    cA
    cN
    cexp
    co
    cdiv
    co
    wceq
    expcld.1
    sqrecd.1
    expsubd.3
    expclzd.3
    cA
    cM
    cN
    expsub
    syl22anc
end
