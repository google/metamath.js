include "cvc.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "co.mm"
include "c2.mm"
include "vcidOLD.mm"
include "oveq12d.mm"
include "caddc.mm"
include "df-2.mm"
include "oveq1i.mm"
include "cc.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "vcdir.mm"
include "mp3anr1.mm"
include "mpanr1.mm"
include "syl5req.mm"
include "eqtr3d.mm"

theorem vc2OLD
  let cA: class A
  let cS: class S
  let cG: class G
  let cW: class W
  let cX: class X
  let vg: setvar g
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  assume vciOLD.1: |- G = ( 1st ` W )
  assume vciOLD.2: |- S = ( 2nd ` W )
  assume vciOLD.3: |- X = ran G


  assert |- ( ( W e. CVecOLD /\ A e. X ) -> ( A G A ) = ( 2 S A ) )

  proof
    cW
    cvc
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    c1
    cA
    cS
    co
    #
    @3
    cG
    co
    #
    cA
    cA
    cG
    co
    c2
    cA
    cS
    co
    #
    @2
    @3
    cA
    @3
    cA
    cG
    cA
    cS
    cG
    cW
    cX
    vciOLD.1
    vciOLD.2
    vciOLD.3
    vcidOLD
    #
    @6
    oveq12d
    @2
    @5
    c1
    c1
    caddc
    co
    #
    cA
    cS
    co
    #
    @4
    c2
    @7
    cA
    cS
    df-2
    oveq1i
    @0
    c1
    cc
    wcel
    #
    @1
    @8
    @4
    wceq
    #
    ax-1cn
    @0
    @9
    @9
    @1
    @10
    ax-1cn
    c1
    c1
    cA
    cS
    cG
    cW
    cX
    vciOLD.1
    vciOLD.2
    vciOLD.3
    vcdir
    mp3anr1
    mpanr1
    syl5req
    eqtr3d
end
