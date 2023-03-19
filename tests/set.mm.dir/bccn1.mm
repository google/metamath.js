include "c1.mm"
include "cbcc.mm"
include "co.mm"
include "cmul.mm"
include "cc0.mm"
include "caddc.mm"
include "cmin.mm"
include "cdiv.mm"
include "cn0.mm"
include "wcel.mm"
include "0nn0.mm"
include "a1i.mm"
include "bccp1k.mm"
include "wceq.mm"
include "0p1e1.mm"
include "oveq2i.mm"
include "bccn0.mm"
include "subid1d.mm"
include "oveq12d.mm"
include "div1d.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"
include "mulid2d.mm"

theorem bccn1
  let wph: wff ph
  let cC: class C
  assume bccn0.c: |- ( ph -> C e. CC )


  assert |- ( ph -> ( C _Cc 1 ) = C )

  proof
    wph
    cC
    c1
    cbcc
    co
    #
    c1
    cC
    cmul
    co
    #
    cC
    wph
    cC
    cc0
    c1
    caddc
    co
    #
    cbcc
    co
    #
    cC
    cc0
    cbcc
    co
    #
    cC
    cc0
    cmin
    co
    #
    @2
    cdiv
    co
    #
    cmul
    co
    @0
    @1
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
    bccp1k
    @3
    @0
    wceq
    wph
    @2
    c1
    cC
    cbcc
    0p1e1
    oveq2i
    a1i
    wph
    @4
    c1
    @6
    cC
    cmul
    wph
    cC
    bccn0.c
    bccn0
    wph
    @6
    cC
    c1
    cdiv
    co
    cC
    wph
    @5
    cC
    @2
    c1
    cdiv
    wph
    cC
    bccn0.c
    subid1d
    @2
    c1
    wceq
    wph
    0p1e1
    a1i
    oveq12d
    wph
    cC
    bccn0.c
    div1d
    eqtrd
    oveq12d
    3eqtr3d
    wph
    cC
    bccn0.c
    mulid2d
    eqtrd
end
