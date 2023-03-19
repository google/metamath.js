include "chil.mm"
include "cc.mm"
include "wf.mm"
include "cc0.mm"
include "c0v.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cnmf.mm"
include "wcel.mm"
include "ax-hv0cl.mm"
include "ffvelrn.mm"
include "mpan2.mm"
include "absge0d.mm"
include "cno.mm"
include "c1.mm"
include "norm0.mm"
include "0le1.mm"
include "eqbrtri.mm"
include "nmfnlb.mm"
include "mp3an23.mm"
include "cxr.mm"
include "wa.mm"
include "wi.mm"
include "abscld.mm"
include "rexrd.mm"
include "nmfnxr.mm"
include "0xr.mm"
include "xrletr.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "mp2and.mm"

theorem nmfnge0
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( T : ~H --> CC -> 0 <_ ( normfn ` T ) )

  proof
    chil
    cc
    cT
    wf
    #
    cc0
    c0v
    cT
    cfv
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    @2
    cT
    cnmf
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
    @0
    c0v
    chil
    wcel
    #
    @1
    cc
    wcel
    ax-hv0cl
    chil
    cc
    c0v
    cT
    ffvelrn
    mpan2
    #
    absge0d
    @0
    @7
    c0v
    cno
    cfv
    #
    c1
    cle
    wbr
    @5
    ax-hv0cl
    @9
    cc0
    c1
    cle
    norm0
    0le1
    eqbrtri
    c0v
    cT
    nmfnlb
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
    @1
    @8
    abscld
    rexrd
    cT
    nmfnxr
    cc0
    cxr
    wcel
    @10
    @11
    @12
    0xr
    cc0
    @2
    @4
    xrletr
    mp3an1
    syl2anc
    mp2and
end
