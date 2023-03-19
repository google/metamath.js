include "cop.mm"
include "co.mm"
include "cpr.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wbr.mm"
include "cif.mm"
include "cle.mm"
include "tmsxpsval.mm"
include "wor.mm"
include "wcel.mm"
include "wceq.mm"
include "xrltso.mm"
include "a1i.mm"
include "cxmt.mm"
include "cfv.mm"
include "xmetcl.mm"
include "syl3anc.mm"
include "suppr.mm"
include "wn.mm"
include "wb.mm"
include "xrltnle.mm"
include "syl2anc.mm"
include "ifbid.mm"
include "ifnot.mm"
include "syl6eq.mm"
include "3eqtrd.mm"

theorem tmsxpsval2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  assume tmsxps.p: |- P = ( dist ` ( ( toMetSp ` M ) Xs. ( toMetSp ` N ) ) )
  assume tmsxps.1: |- ( ph -> M e. ( *Met ` X ) )
  assume tmsxps.2: |- ( ph -> N e. ( *Met ` Y ) )
  assume tmsxpsval.a: |- ( ph -> A e. X )
  assume tmsxpsval.b: |- ( ph -> B e. Y )
  assume tmsxpsval.c: |- ( ph -> C e. X )
  assume tmsxpsval.d: |- ( ph -> D e. Y )


  assert |- ( ph -> ( <. A , B >. P <. C , D >. ) = if ( ( A M C ) <_ ( B N D ) , ( B N D ) , ( A M C ) ) )

  proof
    wph
    cA
    cB
    cop
    cC
    cD
    cop
    cP
    co
    cA
    cC
    cM
    co
    #
    cB
    cD
    cN
    co
    #
    cpr
    cxr
    clt
    csup
    #
    @1
    @0
    clt
    wbr
    #
    @0
    @1
    cif
    #
    @0
    @1
    cle
    wbr
    #
    @1
    @0
    cif
    #
    wph
    cA
    cB
    cC
    cD
    cP
    cM
    cN
    cX
    cY
    tmsxps.p
    tmsxps.1
    tmsxps.2
    tmsxpsval.a
    tmsxpsval.b
    tmsxpsval.c
    tmsxpsval.d
    tmsxpsval
    wph
    cxr
    clt
    wor
    #
    @0
    cxr
    wcel
    #
    @1
    cxr
    wcel
    #
    @2
    @4
    wceq
    @7
    wph
    xrltso
    a1i
    wph
    cM
    cX
    cxmt
    cfv
    wcel
    cA
    cX
    wcel
    cC
    cX
    wcel
    @8
    tmsxps.1
    tmsxpsval.a
    tmsxpsval.c
    cA
    cC
    cM
    cX
    xmetcl
    syl3anc
    #
    wph
    cN
    cY
    cxmt
    cfv
    wcel
    cB
    cY
    wcel
    cD
    cY
    wcel
    @9
    tmsxps.2
    tmsxpsval.b
    tmsxpsval.d
    cB
    cD
    cN
    cY
    xmetcl
    syl3anc
    #
    cxr
    @0
    @1
    clt
    suppr
    syl3anc
    wph
    @4
    @5
    wn
    #
    @0
    @1
    cif
    @6
    wph
    @3
    @12
    @0
    @1
    wph
    @9
    @8
    @3
    @12
    wb
    @11
    @10
    @1
    @0
    xrltnle
    syl2anc
    ifbid
    @5
    @0
    @1
    ifnot
    syl6eq
    3eqtrd
end
