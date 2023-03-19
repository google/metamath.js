include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "co.mm"
include "mulne0bd.mm"
include "mpbi2and.mm"

theorem mulne0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume msq0d.1: |- ( ph -> A e. CC )
  assume mul0ord.2: |- ( ph -> B e. CC )
  assume mulne0d.3: |- ( ph -> A =/= 0 )
  assume mulne0d.4: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( A x. B ) =/= 0 )

  proof
    wph
    cA
    cc0
    wne
    cB
    cc0
    wne
    cA
    cB
    cmul
    co
    cc0
    wne
    mulne0d.3
    mulne0d.4
    wph
    cA
    cB
    msq0d.1
    mul0ord.2
    mulne0bd
    mpbi2and
end
