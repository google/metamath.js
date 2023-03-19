include "cword.mm"
include "wcel.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "c1.mm"
include "cr.mm"
include "w3a.mm"
include "clt.mm"
include "1red.mm"
include "2re.mm"
include "a1i.mm"
include "lencl.mm"
include "nn0red.mm"
include "3jca.mm"
include "adantr.mm"
include "simpr.mm"
include "1lt2.mm"
include "jctil.mm"
include "ltleletr.mm"
include "sylc.mm"
include "wb.mm"
include "wrdlenge1n0.mm"
include "mpbird.mm"

theorem wrdlenge2n0
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ 2 <_ ( # ` W ) ) -> W =/= (/) )

  proof
    cW
    cV
    cword
    wcel
    #
    c2
    cW
    chash
    cfv
    #
    cle
    wbr
    #
    wa
    #
    cW
    c0
    wne
    #
    c1
    @1
    cle
    wbr
    #
    @3
    c1
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    w3a
    #
    c1
    c2
    clt
    wbr
    #
    @2
    wa
    @5
    @0
    @9
    @2
    @0
    @6
    @7
    @8
    @0
    1red
    @7
    @0
    2re
    a1i
    @0
    @1
    cV
    cW
    lencl
    nn0red
    3jca
    adantr
    @3
    @2
    @10
    @0
    @2
    simpr
    1lt2
    jctil
    c1
    c2
    @1
    ltleletr
    sylc
    @0
    @4
    @5
    wb
    @2
    cV
    cW
    wrdlenge1n0
    adantr
    mpbird
end
