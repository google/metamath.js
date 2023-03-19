include "cn0.mm"
include "wcel.mm"
include "c4.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cfmtno.mm"
include "cfv.mm"
include "cprime.mm"
include "simpl.mm"
include "4nn0.mm"
include "a1i.mm"
include "simpr.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "fmtnofz04prm.mm"
include "syl.mm"

theorem fmtnole4prm
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN0 /\ N <_ 4 ) -> ( FermatNo ` N ) e. Prime )

  proof
    cN
    cn0
    wcel
    #
    cN
    c4
    cle
    wbr
    #
    wa
    #
    cN
    cc0
    c4
    cfz
    co
    wcel
    #
    cN
    cfmtno
    cfv
    cprime
    wcel
    @2
    @0
    c4
    cn0
    wcel
    #
    @1
    @3
    @0
    @1
    simpl
    @4
    @2
    4nn0
    a1i
    @0
    @1
    simpr
    cN
    c4
    elfz2nn0
    syl3anbrc
    cN
    fmtnofz04prm
    syl
end
