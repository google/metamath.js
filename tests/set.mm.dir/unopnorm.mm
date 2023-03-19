include "cuo.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "cfv.mm"
include "cno.mm"
include "cr.mm"
include "wf1o.mm"
include "wf.mm"
include "unopf1o.mm"
include "f1of.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "normcl.mm"
include "adantl.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "normge0.mm"
include "csp.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "unop.mm"
include "3anidm23.mm"
include "normsq.mm"
include "3eqtr4d.mm"
include "sq11d.mm"

theorem unopnorm
  let cA: class A
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( ( T e. UniOp /\ A e. ~H ) -> ( normh ` ( T ` A ) ) = ( normh ` A ) )

  proof
    cT
    cuo
    wcel
    #
    cA
    chil
    wcel
    #
    wa
    #
    cA
    cT
    cfv
    #
    cno
    cfv
    #
    cA
    cno
    cfv
    #
    @2
    @3
    chil
    wcel
    #
    @4
    cr
    wcel
    @0
    chil
    chil
    cA
    cT
    @0
    chil
    chil
    cT
    wf1o
    chil
    chil
    cT
    wf
    cT
    unopf1o
    chil
    chil
    cT
    f1of
    syl
    ffvelrnda
    #
    @3
    normcl
    syl
    @1
    @5
    cr
    wcel
    @0
    cA
    normcl
    adantl
    @2
    @6
    cc0
    @4
    cle
    wbr
    @7
    @3
    normge0
    syl
    @1
    cc0
    @5
    cle
    wbr
    @0
    cA
    normge0
    adantl
    @2
    @3
    @3
    csp
    co
    #
    cA
    cA
    csp
    co
    #
    @4
    c2
    cexp
    co
    #
    @5
    c2
    cexp
    co
    #
    @0
    @1
    @8
    @9
    wceq
    cA
    cA
    cT
    unop
    3anidm23
    @2
    @6
    @10
    @8
    wceq
    @7
    @3
    normsq
    syl
    @1
    @11
    @9
    wceq
    @0
    cA
    normsq
    adantl
    3eqtr4d
    sq11d
end
