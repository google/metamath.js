include "cxad.mm"
include "co.mm"
include "cxr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "cicc.mm"
include "wa.mm"
include "elxrge0.mm"
include "sylib.mm"
include "simpld.mm"
include "xaddcld.mm"
include "simprd.mm"
include "xaddge0.mm"
include "syl22anc.mm"
include "sylanbrc.mm"

theorem xrge0addcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xrge0addcld.a: |- ( ph -> A e. ( 0 [,] +oo ) )
  assume xrge0addcld.b: |- ( ph -> B e. ( 0 [,] +oo ) )


  assert |- ( ph -> ( A +e B ) e. ( 0 [,] +oo ) )

  proof
    wph
    cA
    cB
    cxad
    co
    #
    cxr
    wcel
    cc0
    @0
    cle
    wbr
    #
    @0
    cc0
    cpnf
    cicc
    co
    #
    wcel
    wph
    cA
    cB
    wph
    cA
    cxr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wph
    cA
    @2
    wcel
    @3
    @4
    wa
    xrge0addcld.a
    cA
    elxrge0
    sylib
    #
    simpld
    #
    wph
    cB
    cxr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wph
    cB
    @2
    wcel
    @7
    @8
    wa
    xrge0addcld.b
    cB
    elxrge0
    sylib
    #
    simpld
    #
    xaddcld
    wph
    @3
    @7
    @4
    @8
    @1
    @6
    @10
    wph
    @3
    @4
    @5
    simprd
    wph
    @7
    @8
    @9
    simprd
    cA
    cB
    xaddge0
    syl22anc
    @0
    elxrge0
    sylanbrc
end
