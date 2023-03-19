include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "csin.mm"
include "cfv.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "c1.mm"
include "caddc.mm"
include "cz.mm"
include "wceq.mm"
include "negcl.mm"
include "1z.mm"
include "sinper.mm"
include "sylancl.mm"
include "2cn.mm"
include "picn.mm"
include "mulcli.mm"
include "mulid2i.mm"
include "oveq2i.mm"
include "wa.mm"
include "negsubdi.mm"
include "negsubdi2.mm"
include "eqtr3d.mm"
include "mpan2.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "sinneg.mm"

theorem sin2pim
  let cA: class A


  assert |- ( A e. CC -> ( sin ` ( ( 2 x. _pi ) - A ) ) = -u ( sin ` A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cneg
    #
    csin
    cfv
    #
    c2
    cpi
    cmul
    co
    #
    cA
    cmin
    co
    #
    csin
    cfv
    #
    cA
    csin
    cfv
    cneg
    @0
    @1
    c1
    @3
    cmul
    co
    #
    caddc
    co
    #
    csin
    cfv
    #
    @2
    @5
    @0
    @1
    cc
    wcel
    c1
    cz
    wcel
    @8
    @2
    wceq
    cA
    negcl
    1z
    @1
    c1
    sinper
    sylancl
    @0
    @7
    @4
    csin
    @0
    @7
    @1
    @3
    caddc
    co
    #
    @4
    @6
    @3
    @1
    caddc
    @3
    c2
    cpi
    2cn
    picn
    mulcli
    #
    mulid2i
    oveq2i
    @0
    @3
    cc
    wcel
    #
    @9
    @4
    wceq
    @10
    @0
    @11
    wa
    cA
    @3
    cmin
    co
    cneg
    @9
    @4
    cA
    @3
    negsubdi
    cA
    @3
    negsubdi2
    eqtr3d
    mpan2
    syl5eq
    fveq2d
    eqtr3d
    cA
    sinneg
    eqtr3d
end
