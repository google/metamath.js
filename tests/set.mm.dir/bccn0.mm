include "cc0.mm"
include "cbcc.mm"
include "co.mm"
include "cfallfac.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "c1.mm"
include "cn0.mm"
include "wcel.mm"
include "0nn0.mm"
include "a1i.mm"
include "bccval.mm"
include "cc.mm"
include "wceq.mm"
include "fallfac0.mm"
include "syl.mm"
include "fac0.mm"
include "oveq12d.mm"
include "1div1e1.mm"
include "syl6eq.mm"
include "eqtrd.mm"

theorem bccn0
  let wph: wff ph
  let cC: class C
  assume bccn0.c: |- ( ph -> C e. CC )


  assert |- ( ph -> ( C _Cc 0 ) = 1 )

  proof
    wph
    cC
    cc0
    cbcc
    co
    cC
    cc0
    cfallfac
    co
    #
    cc0
    cfa
    cfv
    #
    cdiv
    co
    #
    c1
    wph
    cC
    cc0
    bccn0.c
    cc0
    cn0
    wcel
    wph
    0nn0
    a1i
    bccval
    wph
    @2
    c1
    c1
    cdiv
    co
    c1
    wph
    @0
    c1
    @1
    c1
    cdiv
    wph
    cC
    cc
    wcel
    @0
    c1
    wceq
    bccn0.c
    cC
    fallfac0
    syl
    @1
    c1
    wceq
    wph
    fac0
    a1i
    oveq12d
    1div1e1
    syl6eq
    eqtrd
end
