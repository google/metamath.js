include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cn0.mm"
include "caddc.mm"
include "cz.mm"
include "elfzoel2.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "nn0cn.mm"
include "addcom.mm"
include "syl2an.mm"
include "nn0pzuz.mm"
include "ancoms.mm"
include "eqeltrd.mm"
include "fzoss2.mm"
include "syl.mm"
include "sselda.mm"
include "expcom.mm"
include "mpand.mm"
include "imp.mm"

theorem elfzoext
  let cI: class I
  let cM: class M
  let cN: class N
  let cZ: class Z


  assert |- ( ( Z e. ( M ..^ N ) /\ I e. NN0 ) -> Z e. ( M ..^ ( N + I ) ) )

  proof
    cZ
    cM
    cN
    cfzo
    co
    #
    wcel
    #
    cI
    cn0
    wcel
    #
    cZ
    cM
    cN
    cI
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    @1
    cN
    cz
    wcel
    #
    @2
    @5
    cZ
    cM
    cN
    elfzoel2
    @6
    @2
    wa
    #
    @1
    @5
    @7
    @0
    @4
    cZ
    @7
    @3
    cN
    cuz
    cfv
    #
    wcel
    @0
    @4
    wss
    @7
    @3
    cI
    cN
    caddc
    co
    #
    @8
    @6
    cN
    cc
    wcel
    cI
    cc
    wcel
    @3
    @9
    wceq
    @2
    cN
    zcn
    cI
    nn0cn
    cN
    cI
    addcom
    syl2an
    @2
    @6
    @9
    @8
    wcel
    cI
    cN
    nn0pzuz
    ancoms
    eqeltrd
    cN
    cM
    @3
    fzoss2
    syl
    sselda
    expcom
    mpand
    imp
end
