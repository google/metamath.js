include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cneg.mm"
include "cle.mm"
include "wbr.mm"
include "eluzle.mm"
include "cz.mm"
include "wb.mm"
include "eluzel2.mm"
include "eluzelz.mm"
include "cr.mm"
include "zre.mm"
include "leneg.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "znegcl.mm"
include "eluz.mm"
include "mpbird.mm"

theorem uzneg
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> -u M e. ( ZZ>= ` -u N ) )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    #
    cM
    cneg
    #
    cN
    cneg
    #
    cuz
    cfv
    wcel
    #
    @2
    @1
    cle
    wbr
    #
    @0
    cM
    cN
    cle
    wbr
    #
    @4
    cM
    cN
    eluzle
    @0
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @5
    @4
    wb
    #
    cM
    cN
    eluzel2
    #
    cM
    cN
    eluzelz
    #
    @6
    cM
    cr
    wcel
    cN
    cr
    wcel
    @8
    @7
    cM
    zre
    cN
    zre
    cM
    cN
    leneg
    syl2an
    syl2anc
    mpbid
    @0
    @7
    @6
    @3
    @4
    wb
    #
    @10
    @9
    @7
    @2
    cz
    wcel
    @1
    cz
    wcel
    @11
    @6
    cN
    znegcl
    cM
    znegcl
    @2
    @1
    eluz
    syl2an
    syl2anc
    mpbird
end
