include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cr.mm"
include "0re.mm"
include "1re.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "adantr.mm"
include "wo.mm"
include "halfre.mm"
include "letric.mm"
include "sylancl.mm"
include "orcanai.mm"
include "simp3bi.mm"
include "syl3anbrc.mm"

theorem elii2
  let cX: class X


  assert |- ( ( X e. ( 0 [,] 1 ) /\ -. X <_ ( 1 / 2 ) ) -> X e. ( ( 1 / 2 ) [,] 1 ) )

  proof
    cX
    cc0
    c1
    cicc
    co
    wcel
    #
    cX
    c1
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    wn
    #
    wa
    cX
    cr
    wcel
    #
    @1
    cX
    cle
    wbr
    #
    cX
    c1
    cle
    wbr
    #
    cX
    @1
    c1
    cicc
    co
    wcel
    @0
    @4
    @3
    @0
    @4
    cc0
    cX
    cle
    wbr
    #
    @6
    cc0
    c1
    cX
    0re
    1re
    elicc2i
    #
    simp1bi
    #
    adantr
    @0
    @2
    @5
    @0
    @4
    @1
    cr
    wcel
    @2
    @5
    wo
    @9
    halfre
    cX
    @1
    letric
    sylancl
    orcanai
    @0
    @6
    @3
    @0
    @4
    @7
    @6
    @8
    simp3bi
    adantr
    @1
    c1
    cX
    halfre
    1re
    elicc2i
    syl3anbrc
end
