include "cnlm.mm"
include "wcel.mm"
include "wceq.mm"
include "w3a.mm"
include "csn.mm"
include "cxp.mm"
include "cnmhm.mm"
include "co.mm"
include "clmhm.mm"
include "cnghm.mm"
include "clmod.mm"
include "nlmlmod.mm"
include "id.mm"
include "0lmhm.mm"
include "syl3an.mm"
include "cngp.mm"
include "nlmngp.mm"
include "0nghm.mm"
include "syl2an.mm"
include "3adant3.mm"
include "wa.mm"
include "wb.mm"
include "isnmhm.mm"
include "baib.mm"
include "mpbir2and.mm"

theorem 0nmhm
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cV: class V
  let c.0: class .0.
  assume 0nmhm.1: |- V = ( Base ` S )
  assume 0nmhm.2: |- .0. = ( 0g ` T )
  assume 0nmhm.f: |- F = ( Scalar ` S )
  assume 0nmhm.g: |- G = ( Scalar ` T )


  assert |- ( ( S e. NrmMod /\ T e. NrmMod /\ F = G ) -> ( V X. { .0. } ) e. ( S NMHom T ) )

  proof
    cS
    cnlm
    wcel
    #
    cT
    cnlm
    wcel
    #
    cF
    cG
    wceq
    #
    w3a
    cV
    c.0
    csn
    cxp
    #
    cS
    cT
    cnmhm
    co
    wcel
    #
    @3
    cS
    cT
    clmhm
    co
    wcel
    #
    @3
    cS
    cT
    cnghm
    co
    wcel
    #
    @0
    cS
    clmod
    wcel
    @1
    cT
    clmod
    wcel
    @2
    @2
    @5
    cS
    nlmlmod
    cT
    nlmlmod
    @2
    id
    cV
    cF
    cG
    cS
    cT
    c.0
    0nmhm.2
    0nmhm.1
    0nmhm.f
    0nmhm.g
    0lmhm
    syl3an
    @0
    @1
    @6
    @2
    @0
    cS
    cngp
    wcel
    cT
    cngp
    wcel
    @6
    @1
    cS
    nlmngp
    cT
    nlmngp
    cS
    cT
    cV
    c.0
    0nmhm.1
    0nmhm.2
    0nghm
    syl2an
    3adant3
    @0
    @1
    @4
    @5
    @6
    wa
    #
    wb
    @2
    @4
    @0
    @1
    wa
    @7
    cS
    cT
    @3
    isnmhm
    baib
    3adant3
    mpbir2and
end
