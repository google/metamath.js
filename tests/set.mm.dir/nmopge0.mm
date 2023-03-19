include "chil.mm"
include "wf.mm"
include "cc0.mm"
include "c0v.mm"
include "cfv.mm"
include "cno.mm"
include "cle.mm"
include "wbr.mm"
include "cnop.mm"
include "wcel.mm"
include "ax-hv0cl.mm"
include "ffvelrn.mm"
include "mpan2.mm"
include "normge0.mm"
include "syl.mm"
include "c1.mm"
include "norm0.mm"
include "0le1.mm"
include "eqbrtri.mm"
include "nmoplb.mm"
include "mp3an23.mm"
include "cxr.mm"
include "wa.mm"
include "wi.mm"
include "cr.mm"
include "normcl.mm"
include "rexrd.mm"
include "nmopxr.mm"
include "0xr.mm"
include "xrletr.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "mp2and.mm"

theorem nmopge0
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( T : ~H --> ~H -> 0 <_ ( normop ` T ) )

  proof
    chil
    chil
    cT
    wf
    #
    cc0
    c0v
    cT
    cfv
    #
    cno
    cfv
    #
    cle
    wbr
    #
    @2
    cT
    cnop
    cfv
    #
    cle
    wbr
    #
    cc0
    @4
    cle
    wbr
    #
    @0
    @1
    chil
    wcel
    #
    @3
    @0
    c0v
    chil
    wcel
    #
    @7
    ax-hv0cl
    chil
    chil
    c0v
    cT
    ffvelrn
    mpan2
    #
    @1
    normge0
    syl
    @0
    @8
    c0v
    cno
    cfv
    #
    c1
    cle
    wbr
    @5
    ax-hv0cl
    @10
    cc0
    c1
    cle
    norm0
    0le1
    eqbrtri
    c0v
    cT
    nmoplb
    mp3an23
    @0
    @2
    cxr
    wcel
    #
    @4
    cxr
    wcel
    #
    @3
    @5
    wa
    @6
    wi
    #
    @0
    @2
    @0
    @7
    @2
    cr
    wcel
    @9
    @1
    normcl
    syl
    rexrd
    cT
    nmopxr
    cc0
    cxr
    wcel
    @11
    @12
    @13
    0xr
    cc0
    @2
    @4
    xrletr
    mp3an1
    syl2anc
    mp2and
end
