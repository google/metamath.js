include "c1r.mm"
include "c0r.mm"
include "wceq.mm"
include "cltr.mm"
include "wbr.mm"
include "cnr.mm"
include "wor.mm"
include "wcel.mm"
include "wn.mm"
include "ltsosr.mm"
include "1sr.mm"
include "sonr.mm"
include "mp2an.mm"
include "0lt1sr.mm"
include "breq1.mm"
include "mpbiri.mm"
include "mto.mm"

theorem 1ne0sr



  assert |- -. 1R = 0R

  proof
    c1r
    c0r
    wceq
    #
    c1r
    c1r
    cltr
    wbr
    #
    cnr
    cltr
    wor
    c1r
    cnr
    wcel
    @1
    wn
    ltsosr
    1sr
    cnr
    c1r
    cltr
    sonr
    mp2an
    @0
    @1
    c0r
    c1r
    cltr
    wbr
    0lt1sr
    c1r
    c0r
    c1r
    cltr
    breq1
    mpbiri
    mto
end
