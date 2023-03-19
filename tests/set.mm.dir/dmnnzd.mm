include "cdmn.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "ccring.mm"
include "cgi.mm"
include "cfv.mm"
include "wne.mm"
include "eqid.mm"
include "isdmn3.mm"
include "simp3bi.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "orbi1d.mm"
include "imbi12d.mm"
include "oveq2.mm"
include "orbi2d.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "expd.mm"
include "3imp2.mm"

theorem dmnnzd
  let cA: class A
  let cB: class B
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  assume dmnnzd.1: |- G = ( 1st ` R )
  assume dmnnzd.2: |- H = ( 2nd ` R )
  assume dmnnzd.3: |- X = ran G
  assume dmnnzd.4: |- Z = ( GId ` G )


  assert |- ( ( R e. Dmn /\ ( A e. X /\ B e. X /\ ( A H B ) = Z ) ) -> ( A = Z \/ B = Z ) )

  proof
    cR
    cdmn
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    cB
    cH
    co
    #
    cZ
    wceq
    #
    cA
    cZ
    wceq
    #
    cB
    cZ
    wceq
    #
    wo
    #
    @0
    @1
    @2
    @4
    @7
    wi
    #
    @0
    va
    cv
    #
    vb
    cv
    #
    cH
    co
    #
    cZ
    wceq
    #
    @9
    cZ
    wceq
    #
    @10
    cZ
    wceq
    #
    wo
    #
    wi
    #
    vb
    cX
    wral
    va
    cX
    wral
    #
    @1
    @2
    wa
    @8
    @0
    cR
    ccring
    wcel
    cH
    cgi
    cfv
    #
    cZ
    wne
    @17
    cR
    @18
    cG
    cH
    cX
    cZ
    va
    vb
    dmnnzd.1
    dmnnzd.2
    dmnnzd.3
    dmnnzd.4
    @18
    eqid
    isdmn3
    simp3bi
    @16
    @8
    cA
    @10
    cH
    co
    #
    cZ
    wceq
    #
    @5
    @14
    wo
    #
    wi
    va
    vb
    cA
    cB
    cX
    cX
    @9
    cA
    wceq
    #
    @12
    @20
    @15
    @21
    @22
    @11
    @19
    cZ
    @9
    cA
    @10
    cH
    oveq1
    eqeq1d
    @22
    @13
    @5
    @14
    @9
    cA
    cZ
    eqeq1
    orbi1d
    imbi12d
    @10
    cB
    wceq
    #
    @20
    @4
    @21
    @7
    @23
    @19
    @3
    cZ
    @10
    cB
    cA
    cH
    oveq2
    eqeq1d
    @23
    @14
    @6
    @5
    @10
    cB
    cZ
    eqeq1
    orbi2d
    imbi12d
    rspc2v
    syl5com
    expd
    3imp2
end
