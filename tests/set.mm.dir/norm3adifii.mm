include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "hvsubcli.mm"
include "normcli.mm"
include "recni.mm"
include "negsubdi2i.mm"
include "caddc.mm"
include "norm3difi.mm"
include "normsubi.mm"
include "oveq1i.mm"
include "breqtri.mm"
include "lesubaddi.mm"
include "mpbir.mm"
include "eqbrtri.mm"
include "resubcli.mm"
include "lenegcon1i.mm"
include "mpbi.mm"
include "abslei.mm"
include "mpbir2an.mm"

theorem norm3adifii
  let cA: class A
  let cB: class B
  let cC: class C
  assume norm3dif.1: |- A e. ~H
  assume norm3dif.2: |- B e. ~H
  assume norm3dif.3: |- C e. ~H


  assert |- ( abs ` ( ( normh ` ( A -h C ) ) - ( normh ` ( B -h C ) ) ) ) <_ ( normh ` ( A -h B ) )

  proof
    cA
    cC
    cmv
    co
    #
    cno
    cfv
    #
    cB
    cC
    cmv
    co
    #
    cno
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    cA
    cB
    cmv
    co
    #
    cno
    cfv
    #
    cle
    wbr
    @6
    cneg
    @4
    cle
    wbr
    #
    @4
    @6
    cle
    wbr
    #
    @4
    cneg
    #
    @6
    cle
    wbr
    @7
    @9
    @3
    @1
    cmin
    co
    #
    @6
    cle
    @1
    @3
    @1
    @0
    cA
    cC
    norm3dif.1
    norm3dif.3
    hvsubcli
    normcli
    #
    recni
    @3
    @2
    cB
    cC
    norm3dif.2
    norm3dif.3
    hvsubcli
    normcli
    #
    recni
    negsubdi2i
    @10
    @6
    cle
    wbr
    @3
    @6
    @1
    caddc
    co
    #
    cle
    wbr
    @3
    cB
    cA
    cmv
    co
    cno
    cfv
    #
    @1
    caddc
    co
    @13
    cle
    cB
    cC
    cA
    norm3dif.2
    norm3dif.3
    norm3dif.1
    norm3difi
    @14
    @6
    @1
    caddc
    cB
    cA
    norm3dif.2
    norm3dif.1
    normsubi
    oveq1i
    breqtri
    @3
    @1
    @6
    @12
    @11
    @5
    cA
    cB
    norm3dif.1
    norm3dif.2
    hvsubcli
    normcli
    #
    lesubaddi
    mpbir
    eqbrtri
    @4
    @6
    @1
    @3
    @11
    @12
    resubcli
    #
    @15
    lenegcon1i
    mpbi
    @8
    @1
    @6
    @3
    caddc
    co
    cle
    wbr
    cA
    cC
    cB
    norm3dif.1
    norm3dif.3
    norm3dif.2
    norm3difi
    @1
    @3
    @6
    @11
    @12
    @15
    lesubaddi
    mpbir
    @4
    @6
    @16
    @15
    abslei
    mpbir2an
end
