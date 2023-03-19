include "chil.mm"
include "wcel.mm"
include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "cno.mm"
include "cle.mm"
include "pjcoi.mm"
include "fveq2d.mm"
include "cch.mm"
include "wbr.mm"
include "pjhcli.mm"
include "pjnorm.mm"
include "sylancr.mm"
include "eqbrtrd.mm"

theorem pjs14i
  let cA: class A
  let cG: class G
  let cH: class H
  assume pjs14.1: |- G e. CH
  assume pjs14.2: |- H e. CH


  assert |- ( A e. ~H -> ( normh ` ( ( ( projh ` H ) o. ( projh ` G ) ) ` A ) ) <_ ( normh ` ( ( projh ` G ) ` A ) ) )

  proof
    cA
    chil
    wcel
    #
    cA
    cH
    cpjh
    cfv
    #
    cG
    cpjh
    cfv
    #
    ccom
    cfv
    #
    cno
    cfv
    cA
    @2
    cfv
    #
    @1
    cfv
    #
    cno
    cfv
    #
    @4
    cno
    cfv
    #
    cle
    @0
    @3
    @5
    cno
    cA
    cH
    cG
    pjs14.2
    pjs14.1
    pjcoi
    fveq2d
    @0
    cH
    cch
    wcel
    @4
    chil
    wcel
    @6
    @7
    cle
    wbr
    pjs14.2
    cA
    cG
    pjs14.1
    pjhcli
    @4
    cH
    pjnorm
    sylancr
    eqbrtrd
end
