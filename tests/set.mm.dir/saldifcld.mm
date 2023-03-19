include "csalg.mm"
include "wcel.mm"
include "cuni.mm"
include "cdif.mm"
include "saldifcl.mm"
include "syl2anc.mm"

theorem saldifcld
  let wph: wff ph
  let cS: class S
  let cE: class E
  let vk: setvar k
  let vx: setvar x
  assume saldifcld.1: |- ( ph -> S e. SAlg )
  assume saldifcld.2: |- ( ph -> E e. S )


  assert |- ( ph -> ( U. S \ E ) e. S )

  proof
    wph
    cS
    csalg
    wcel
    cE
    cS
    wcel
    cS
    cuni
    cE
    cdif
    cS
    wcel
    saldifcld.1
    saldifcld.2
    cS
    cE
    saldifcl
    syl2anc
end
