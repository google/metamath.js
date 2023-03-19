include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "cres.mm"
include "dssmapnvod.mm"
include "coeq1d.mm"
include "wf1o.mm"
include "wceq.mm"
include "dssmapf1od.mm"
include "f1ococnv1.mm"
include "syl.mm"
include "eqtr3d.mm"

theorem dssmap2d
  let wph: wff ph
  let cB: class B
  let cD: class D
  let vf: setvar f
  let cO: class O
  let cV: class V
  let vs: setvar s
  let vb: setvar b
  assume dssmapfvd.o: |- O = ( b e. _V |-> ( f e. ( ~P b ^m ~P b ) |-> ( s e. ~P b |-> ( b \ ( f ` ( b \ s ) ) ) ) ) )
  assume dssmapfvd.d: |- D = ( O ` B )
  assume dssmapfvd.b: |- ( ph -> B e. V )

  disjoint B b
  disjoint B f
  disjoint B s
  disjoint b f
  disjoint b s
  disjoint f s
  disjoint b ph
  disjoint f ph
  disjoint ph s
  assert |- ( ph -> ( D o. D ) = ( _I |` ( ~P B ^m ~P B ) ) )

  proof
    wph
    cD
    ccnv
    #
    cD
    ccom
    #
    cD
    cD
    ccom
    cid
    cB
    cpw
    #
    @2
    cmap
    co
    #
    cres
    #
    wph
    @0
    cD
    cD
    wph
    cB
    cD
    vf
    cO
    cV
    vs
    vb
    dssmapfvd.o
    dssmapfvd.d
    dssmapfvd.b
    dssmapnvod
    coeq1d
    wph
    @3
    @3
    cD
    wf1o
    @1
    @4
    wceq
    wph
    cB
    cD
    vf
    cO
    cV
    vs
    vb
    dssmapfvd.o
    dssmapfvd.d
    dssmapfvd.b
    dssmapf1od
    @3
    @3
    cD
    f1ococnv1
    syl
    eqtr3d
end
