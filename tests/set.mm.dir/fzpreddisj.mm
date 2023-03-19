include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "csn.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cin.mm"
include "c0.mm"
include "incom.mm"
include "wn.mm"
include "wceq.mm"
include "cz.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cc0.mm"
include "clt.mm"
include "0lt1.mm"
include "0re.mm"
include "1re.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "cr.mm"
include "wb.mm"
include "eluzel2.mm"
include "zred.mm"
include "leaddle0.mm"
include "sylancl.mm"
include "mtbiri.mm"
include "intnanrd.mm"
include "intnand.mm"
include "elfz2.mm"
include "sylnibr.mm"
include "disjsn.mm"
include "sylibr.mm"
include "syl5eq.mm"

theorem fzpreddisj
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> ( { M } i^i ( ( M + 1 ) ... N ) ) = (/) )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    #
    cM
    csn
    #
    cM
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    cin
    @3
    @1
    cin
    #
    c0
    @1
    @3
    incom
    @0
    cM
    @3
    wcel
    #
    wn
    @4
    c0
    wceq
    @0
    @2
    cz
    wcel
    cN
    cz
    wcel
    cM
    cz
    wcel
    w3a
    #
    @2
    cM
    cle
    wbr
    #
    cM
    cN
    cle
    wbr
    #
    wa
    #
    wa
    @5
    @0
    @9
    @6
    @0
    @7
    @8
    @0
    @7
    c1
    cc0
    cle
    wbr
    #
    cc0
    c1
    clt
    wbr
    @10
    wn
    0lt1
    cc0
    c1
    0re
    1re
    ltnlei
    mpbi
    @0
    cM
    cr
    wcel
    c1
    cr
    wcel
    @7
    @10
    wb
    @0
    cM
    cM
    cN
    eluzel2
    zred
    1re
    cM
    c1
    leaddle0
    sylancl
    mtbiri
    intnanrd
    intnand
    cM
    @2
    cN
    elfz2
    sylnibr
    @3
    cM
    disjsn
    sylibr
    syl5eq
end
