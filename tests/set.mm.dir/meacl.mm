include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "id.mm"
include "meaf.mm"
include "ffvelrnda.mm"
include "syl2anc.mm"

theorem meacl
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume meacl.1: |- ( ph -> M e. Meas )
  assume meacl.2: |- S = dom M
  assume meacl.3: |- ( ph -> A e. S )


  assert |- ( ph -> ( M ` A ) e. ( 0 [,] +oo ) )

  proof
    wph
    wph
    cA
    cS
    wcel
    cA
    cM
    cfv
    cc0
    cpnf
    cicc
    co
    #
    wcel
    wph
    id
    meacl.3
    wph
    cS
    @0
    cA
    cM
    wph
    cS
    cM
    meacl.1
    meacl.2
    meaf
    ffvelrnda
    syl2anc
end
