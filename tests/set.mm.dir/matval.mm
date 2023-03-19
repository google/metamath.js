include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cmat.mm"
include "co.mm"
include "cnx.mm"
include "cmulr.mm"
include "cfv.mm"
include "cop.mm"
include "csts.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "cxp.mm"
include "cfrlm.mm"
include "cotp.mm"
include "cmmul.mm"
include "id.mm"
include "sqxpeqd.mm"
include "oveqan12rd.mm"
include "syl6eqr.mm"
include "oteq123d.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "df-mat.mm"
include "ovex.mm"
include "ovmpt2a.mm"
include "sylan2.mm"
include "syl5eq.mm"

theorem matval
  let cA: class A
  let cR: class R
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vr: setvar r
  assume matval.a: |- A = ( N Mat R )
  assume matval.g: |- G = ( R freeLMod ( N X. N ) )
  assume matval.t: |- .x. = ( R maMul <. N , N , N >. )


  assert |- ( ( N e. Fin /\ R e. V ) -> A = ( G sSet <. ( .r ` ndx ) , .x. >. ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    cV
    wcel
    #
    wa
    cA
    cN
    cR
    cmat
    co
    #
    cG
    cnx
    cmulr
    cfv
    #
    c.x
    cop
    #
    csts
    co
    #
    matval.a
    @1
    @0
    cR
    cvv
    wcel
    @2
    @5
    wceq
    cR
    cV
    elex
    vn
    vr
    cN
    cR
    cfn
    cvv
    vr
    cv
    #
    vn
    cv
    #
    @7
    cxp
    #
    cfrlm
    co
    #
    @3
    @6
    @7
    @7
    @7
    cotp
    #
    cmmul
    co
    #
    cop
    #
    csts
    co
    @5
    cmat
    @7
    cN
    wceq
    #
    @6
    cR
    wceq
    #
    wa
    #
    @9
    cG
    @12
    @4
    csts
    @15
    @9
    cR
    cN
    cN
    cxp
    #
    cfrlm
    co
    cG
    @14
    @13
    @6
    cR
    @8
    @16
    cfrlm
    @14
    id
    #
    @13
    @7
    cN
    @13
    id
    #
    sqxpeqd
    oveqan12rd
    matval.g
    syl6eqr
    @15
    @11
    c.x
    @3
    @15
    @11
    cR
    cN
    cN
    cN
    cotp
    #
    cmmul
    co
    c.x
    @14
    @13
    @6
    cR
    @10
    @19
    cmmul
    @17
    @13
    @7
    cN
    @7
    cN
    @7
    cN
    @18
    @18
    @18
    oteq123d
    oveqan12rd
    matval.t
    syl6eqr
    opeq2d
    oveq12d
    vn
    vr
    df-mat
    cG
    @4
    csts
    ovex
    ovmpt2a
    sylan2
    syl5eq
end
