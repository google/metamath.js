include "cmnf.mm"
include "cxr.mm"
include "wcel.mm"
include "mnfxr.mm"
include "a1i.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "0xr.mm"
include "clt.mm"
include "wbr.mm"
include "mnflt0.mm"
include "cle.mm"
include "pnfxr.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "xrltletrd.mm"
include "xrgtned.mm"

theorem xrge0nemnfd
  let wph: wff ph
  let cA: class A
  assume xrge0nemnfd.1: |- ( ph -> A e. ( 0 [,] +oo ) )


  assert |- ( ph -> A =/= -oo )

  proof
    wph
    cmnf
    cA
    cmnf
    cxr
    wcel
    wph
    mnfxr
    a1i
    #
    wph
    cc0
    cpnf
    cicc
    co
    #
    cxr
    cA
    cc0
    cpnf
    iccssxr
    xrge0nemnfd.1
    sseldi
    #
    wph
    cmnf
    cc0
    cA
    @0
    cc0
    cxr
    wcel
    #
    wph
    0xr
    a1i
    #
    @2
    cmnf
    cc0
    clt
    wbr
    wph
    mnflt0
    a1i
    wph
    @3
    cpnf
    cxr
    wcel
    #
    cA
    @1
    wcel
    cc0
    cA
    cle
    wbr
    @4
    @5
    wph
    pnfxr
    a1i
    xrge0nemnfd.1
    cc0
    cpnf
    cA
    iccgelb
    syl3anc
    xrltletrd
    xrgtned
end
