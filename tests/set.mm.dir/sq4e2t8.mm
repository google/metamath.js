include "c4.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "c8.mm"
include "2t2e4.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "2cn.mm"
include "sqmuli.mm"
include "sqvali.mm"
include "sq2.mm"
include "oveq12i.mm"
include "4cn.mm"
include "mulassi.mm"
include "4t2e8.mm"
include "mulcomli.mm"
include "oveq2i.mm"
include "3eqtri.mm"

theorem sq4e2t8



  assert |- ( 4 ^ 2 ) = ( 2 x. 8 )

  proof
    c4
    c2
    cexp
    co
    c2
    c2
    cmul
    co
    #
    c2
    cexp
    co
    c2
    c2
    cexp
    co
    #
    @1
    cmul
    co
    #
    c2
    c8
    cmul
    co
    #
    c4
    @0
    c2
    cexp
    @0
    c4
    2t2e4
    eqcomi
    oveq1i
    c2
    c2
    2cn
    2cn
    sqmuli
    @2
    @0
    c4
    cmul
    co
    c2
    c2
    c4
    cmul
    co
    #
    cmul
    co
    @3
    @1
    @0
    @1
    c4
    cmul
    c2
    2cn
    sqvali
    sq2
    oveq12i
    c2
    c2
    c4
    2cn
    2cn
    4cn
    mulassi
    @4
    c8
    c2
    cmul
    c4
    c2
    c8
    4cn
    2cn
    4t2e8
    mulcomli
    oveq2i
    3eqtri
    3eqtri
end
