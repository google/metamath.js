include "cc0.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cioo.mm"
include "wcel.mm"
include "ctan.mm"
include "cfv.mm"
include "csin.mm"
include "ccos.mm"
include "crp.mm"
include "cc.mm"
include "wne.mm"
include "wceq.mm"
include "elioore.mm"
include "recnd.mm"
include "recoscld.mm"
include "clt.mm"
include "wbr.mm"
include "sincosq1sgn.mm"
include "simprd.mm"
include "elrpd.mm"
include "rpne0d.mm"
include "tanval.mm"
include "syl2anc.mm"
include "resincld.mm"
include "simpld.mm"
include "rpdivcld.mm"
include "eqeltrd.mm"

theorem tanrpcl
  let cA: class A


  assert |- ( A e. ( 0 (,) ( _pi / 2 ) ) -> ( tan ` A ) e. RR+ )

  proof
    cA
    cc0
    cpi
    c2
    cdiv
    co
    #
    cioo
    co
    wcel
    #
    cA
    ctan
    cfv
    #
    cA
    csin
    cfv
    #
    cA
    ccos
    cfv
    #
    cdiv
    co
    #
    crp
    @1
    cA
    cc
    wcel
    @4
    cc0
    wne
    @2
    @5
    wceq
    @1
    cA
    cA
    cc0
    @0
    elioore
    #
    recnd
    @1
    @4
    @1
    @4
    @1
    cA
    @6
    recoscld
    @1
    cc0
    @3
    clt
    wbr
    #
    cc0
    @4
    clt
    wbr
    #
    cA
    sincosq1sgn
    #
    simprd
    elrpd
    #
    rpne0d
    cA
    tanval
    syl2anc
    @1
    @3
    @4
    @1
    @3
    @1
    cA
    @6
    resincld
    @1
    @7
    @8
    @9
    simpld
    elrpd
    @10
    rpdivcld
    eqeltrd
end
